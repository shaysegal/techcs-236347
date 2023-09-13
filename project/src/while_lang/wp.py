import sys
from pathlib import Path
import math
import ast
path_root = Path(__file__).parents[2]
sys.path.append(str(path_root)+'/lib')
sys.path.append(str(path_root)+'/src')
from adt.tree.walk import PreorderWalk, InorderWalk, PostorderWalk
from syntax import ExpressionWhileParser,WhileParser
import operator
import re
import inspect
from top_down import while_tree_to_z3,generate_programs_by_depth,ast_to_z3
from z3 import Int,String, ForAll, Implies, Not, And, Or, Solver, unsat, sat,Length,Concat,IndexOf
import z3
old_prog = None

OP = {'+': operator.add, '-': operator.sub,
      '*': operator.mul, '/': operator.truediv,#'/': operator.floordiv
      '!=': operator.ne, '>': operator.gt, '<': operator.lt,
      '<=': operator.le, '>=': operator.ge, '=': operator.eq, '%': operator.mod,
        'concat':Concat,
        "indexof":IndexOf #return int and not string
    }
REVERSE_OP = {'+': operator.sub, '-': operator.add,
      '*': operator.truediv, '/': operator.mul,#'/': operator.floordiv
      '!=': operator.eq, '>': operator.le, '<': operator.ge,
      '<=': operator.gt, '>=': operator.lt, '=': operator.ne,
        'concat':lambda a,b : a[0:str.index(a,b,-1)] if b in a else a,
        "indexof":IndexOf #return int and not string
    }
UNARY_OP={'len':Length,#UnaryOP, might need something else - also - return int and not string
}
terminals = set(["skip","string_element", "num", "+", "-", "*", "/", "if", "then", "else", "while", "do", ";",":=", "(", ")","concat","indexof","len"])
non_terminals = set(["S", "S1", "E", "E_num","E_string"])
grammar_rules = {
    "S": ["S1", "S1 ; S"],
    "S1": ["skip", "id := E", "if E then S else S1", "while E do S1", "( S )"],
    "E": ["E_num", "E_num OP E_num"," E_string","E_string OP_STRING E_string","UNARY_STRING_OP E_string"],
    "OP": ["+", "-", "*", "/"],
    "OP_STRING":["concat","indexof"],
    "UNARY_STRING_OP":["len"],
    "E_num": [ "num", "( E )"],
    "E_string": [ "string_element", "( E )"]
}

def mk_env(pvars,types):
    return {v : types[v](v) for v in pvars}


def upd(env, v, expr):
    env = env.copy()
    env[v] = expr
    return env
def transform_reverse_cond(cond,env):
    #should transfrom string to Z3 formual using OP dictionary   
    for node in PreorderWalk(cond):
        if node.root in OP:
            return REVERSE_OP[node.root](transform_reverse_cond(node.subtrees[0],  env),transform_reverse_cond(node.subtrees[1],  env))
        elif node.root in UNARY_OP:
            return UNARY_OP[node.root](transform_reverse_cond(node.subtrees[0], env))
        else:
            return env[node.subtrees[0].root] if node.subtrees[0].root in env else node.subtrees[0].root

def transform_cond(cond,env):
    #should transfrom string to Z3 formual using OP dictionary   
    for node in PreorderWalk(cond):
        if node.root in OP:
            return OP[node.root](transform_cond(node.subtrees[0],  env),transform_cond(node.subtrees[1],  env))
        elif node.root in UNARY_OP:
            return UNARY_OP[node.root](transform_cond(node.subtrees[0], env))
        else:
            return env[node.subtrees[0].root] if node.subtrees[0].root in env else node.subtrees[0].root
        
def extract_values_from_Q(Q,env):
    # raise NotImplemented
    values = {}
    # values.update(env)
    # result = P(env)
    all_var_regx = "|".join(env.keys())
    for arg in Q.split('and'):#inspect.getsource(Q).split('and'):
        # if(arg.endswith('\n')):
        #     arg = arg[:-1] + ' '
        var,value = re.findall(f'd\[\'[{all_var_regx}]+\'\]==.+',arg.replace(" ",""))[0].split('==')
        var = var.split('[')[1].strip("]'")
        values[var] = eval(value)

    return values

def check_current_values_againt_program(prog,Q_values,post_id):
    variables = Q_values.copy()
    def evaluate_expression(expr):
        if isinstance(expr, int):
            return expr  # If it's already an integer, return it
        elif isinstance(expr, str):
            if expr in variables:
                return variables[expr]  # If it's a variable, return its value
            else:
                raise ValueError(f"Variable {expr} is not defined.")
        elif isinstance(expr, tuple) and len(expr) == 3:
            op = expr[1]
            left_value = evaluate_expression(expr[0])
            right_value = evaluate_expression(expr[2])

            if op == '+':
                return left_value + right_value
            elif op == '-':
                return left_value - right_value
            elif op == '*':
                return left_value * right_value
            elif op == '/':
                if right_value != 0:
                    return left_value / right_value
                else:
                    raise ValueError("Division by zero.")
            else:
                raise ValueError(f"Unsupported operator: {op}")
        else:
            raise ValueError(f"Invalid expression: {expr}")

    try:
        if prog == post_id: return False
        result = evaluate_expression('a + b')
        result = evaluate_expression(prog)
        if result == Q_values[post_id]:
            print(f"Program {prog} produces the expected value {result} for {post_id}.")
            return True
        else:
            return False
    except ValueError as e:
        print(f"Error: {e}")
        return False


def send_to_synt_assert(assert_cond,post_id,templete_prog,env):
    global grammar_rules,terminals
    var_types = env["types"]
    varables = env.copy()
    del varables['types']
    del varables[post_id]
    for var in varables:
        if var_types[var] == Int :
            grammar_rules['E_num'] = [var]+ grammar_rules['E_num']
            continue
        if var_types[var] == String :
            grammar_rules['E_string'] = [var]+ grammar_rules['E_string']
            continue
        raise ValueError()
    
    terminals.update(varables.keys())
    z3_lut={}
    for values in varables:
        z3_type_ctor=var_types[values]
        z3_lut[values]=z3_type_ctor(values)
    for program in generate_programs_by_depth("E", 5,grammar_rules,terminals):
        sol = Solver()
        temp_prog = templete_prog.replace("??",program)
        full_program = assert_cond.replace(post_id,temp_prog)
        try:
            full_program = full_program.replace("=",'==')
            free_vars = []
            z3_prog = ast_to_z3(ast.parse(full_program,mode='eval'),z3_lut,free_vars)
        except Exception as e:
            # print("z3 Error")
            continue
        formula = z3.ForAll(list(z3_lut.values()),z3_prog)
        #if free_vars:
        #    formula = z3.Exists(free_vars, formula)
        sol.add(formula)
        status = sol.check()
        if status == sat:
            m = sol.model()
            for num in list(filter(lambda v: v.startswith("num"),map(lambda v: str(v),m.decls()))):
                program = program.replace(num,str(m[Int(num)]))
            for string_element in list(filter(lambda v: v.startswith("string_element"),map(lambda v: str(v),m.decls()))):
                program = program.replace(string_element,str(m[String(string_element)]))
            return program

def send_to_synt_pbe(values_array,post_id,env,template):
    global grammar_rules,terminals
    var_types = env["types"]
    expected_value = values_array[0][post_id]
    prog_values  = values_array[0].copy()
    del prog_values[post_id]
    for var in prog_values.keys():
        if var_types[var] == Int and not var in grammar_rules['E_num']:
            grammar_rules['E_num'] = [var]+ grammar_rules['E_num']
            continue
        if var_types[var] == String and not var in grammar_rules['E_string']:
            grammar_rules['E_string'] = [var]+ grammar_rules['E_string']
            continue
    
    terminals.update(prog_values.keys())
    for program in generate_programs_by_depth("E", 5,grammar_rules,terminals):
        # print("debug program",program)
        sol = Solver()
        should_check=True
        for example_number,values in enumerate(values_array):
            expected_value = values[post_id]
            z3_lut={}
            for k in values.keys():
                z3_type_ctor=var_types[k]
                z3_lut[k]=z3_type_ctor(k+str(example_number))
            try:
                full_program = template.replace("??",program)
                z3_prog = while_tree_to_z3(ExpressionWhileParser()(full_program),z3_lut)
            except Exception as e:
                #print("z3 Error")
                should_check=False
                break
            formula = None
            try:
                formula = operator.eq(z3_prog,expected_value)
            except Exception as e:
               # print("z3 Error")
                should_check=False
                break
            sol.add(formula)
            for key,val in values.items():
                sol.add(val == z3_lut[key])
        if not should_check:
            continue
        status = sol.check()
        if status == sat:
            m = sol.model()
            for num in list(filter(lambda v: v.startswith("num"),map(lambda v: str(v),m.decls()))):
                program = program.replace(num,str(m[Int(num)]))
            for string_element in list(filter(lambda v: v.startswith("string_element"),map(lambda v: str(v),m.decls()))):
                program = program.replace(string_element,str(m[String(string_element)]))
            return program
    print("done")
def inner_verify(P, ast, Q, env ,linv,global_env):
    global old_prog
    match ast.root :
        case ";":
            #seq 
            #M=None
            #inner_lambda = inner_verify(P,ast.subtrees[1],Q,env,linv)
            wp_c2=lambda new_env : inner_verify(P,ast.subtrees[1],Q,new_env.copy(),linv,global_env)
            return inner_verify(P,ast.subtrees[0],wp_c2,env,linv,global_env)
        case ":=":
            #assign
            v,expr = ast.subtrees
            e_at_x = upd(env,str(transform_cond(v,env)),transform_cond(expr,env))
            return Q(e_at_x)
            #something with z3
        case "while":

            P = linv
            b , c = ast.subtrees
            b = transform_cond(b, global_env)
            while_env = global_env.copy()
            for idx,key in enumerate(global_env.keys()):
                while_env[key]=Int(key+str(idx)) if type(global_env[key]) == z3.ArithRef else String(key+str(idx))

            return And(P(env),
                       ForAll([while_env[z3val] for z3val in filter(lambda val : val in c.terminals ,while_env.keys())],                  
                              And(
                                Implies(
                                    And(P(while_env),b),
                                        inner_verify(P,c,linv,while_env.copy(),linv,while_env)),
                                Implies(
                                    And(P(while_env),Not(b)),
                                        Q(while_env))
                                  )
                                )
                        )


        case "if":    

            b ,c_1,c_2 = ast.subtrees
            b = transform_cond(b, env)
            return Or(And(b,inner_verify(P,c_1,Q,env,linv,global_env)),And(Not(b),inner_verify(P,c_2,Q,env,linv,global_env)))
        case "skip":    
            return Q(env)
    return 

def sketch_verify(P, ast, Q, env ,linv,global_env):
    global old_prog
    match ast.root :
        case ";":
            wp_c2=lambda new_env : sketch_verify(P,ast.subtrees[1],Q,new_env.copy(),linv,global_env)  
            return sketch_verify(P,ast.subtrees[0],wp_c2,env,linv,global_env)
        case ":=":
            #assign
            #t = x * ?? -> Tree(x , * , sketch)
            if ast.subtrees[1].root == "sketch":
                template = "??"
                post_id = ast.subtrees[0].subtrees[0].root
                #Q_values = extract_values_from_Q(Q,env)
                return post_id, None , template
            if "??" in ast.subtrees[1].terminals:
                #TODO: inorder tree walk to get program
                template = ""
                for node in InorderWalk(ast.subtrees[1]):
                    if node.root == "id" or node.root == "sketch": continue
                    template += node.root
                    template += " "
                template = template[:-1]
                post_id = ast.subtrees[0].subtrees[0].root
                #Q_values = extract_values_from_Q(Q,env)
                return post_id, None, template
            v,expr = ast.subtrees
            e_at_x = upd(env,str(transform_cond(v,env)),transform_cond(expr,env))
            return Q(e_at_x)
            #something with z3
        case "while":

            P = linv
            b , c = ast.subtrees
            b = transform_cond(b, global_env)
            return And(P(env),
                       ForAll(list(global_env.values()),                  
                              And(
                                Implies(
                                    And(P(global_env),b),
                                        sketch_verify(P,c,linv,global_env.copy(),linv,global_env)),
                                Implies(
                                    And(P(global_env),Not(b)),
                                        Q(global_env))
                                  )
                                )
                        )


        case "if":    
            b ,c_1,c_2 = ast.subtrees
            b = transform_cond(b, env)
            return Or(And(b,sketch_verify(P,c_1,Q,env,linv,global_env)),And(Not(b),sketch_verify(P,c_2,Q,env,linv,global_env)))
        case "skip":    
            return Q(env)
    return 



def verify(P, ast, Q, pvars,linv=None,env=None,text_prog=None):
    """
    Verifies a Hoare triple {P} c {Q}
    Where P, Q are assertions (see below for examples)
    and ast is the AST of the command c.
    Returns `True` iff the triple is valid.
    Also prints the counterexample (model) returned from Z3 in case
    it is not.
    """
    #P,Q
    # pvars = ['a','b','sum']#set(filter(lambda t: type(t) == str and t!='skip' ,ast.terminals))
    ret = inner_verify(P, ast, Q, env.copy(),linv,env.copy())
    sol = Solver()
    formula = Implies(P(env),ret)
    sol.add(Not(formula))
    status = sol.check()
    if status == sat:
        text_prog.insert("end", ">> Invalid.\n", "title")
        m = sol.model()
        return False , m
    text_prog.insert("end", ">> Valid.\n", "title")
    return True ,None 

    # ...
def check_aginst_current_program(god_program,values,post_id,env):
    var_types=env["types"]
    expected_value = values[post_id]
    sol = Solver()
    z3_lut={}
    for k in values.keys():
        z3_type_ctor=var_types[k]
        z3_lut[k]=z3_type_ctor(k)
    z3_prog = ast_to_z3(ast.parse(god_program,mode='eval'),z3_lut)
    formula = operator.eq(z3_prog,expected_value)
    sol.add(formula)
    for key,val in values.items():
        sol.add(val == z3_lut[key])

    status = sol.check()
    return status == sat

def get_sketch_program(ast):
    for node in PreorderWalk(ast):
        if node.root == ":=":
            if "??" in node.subtrees[1].terminals:
                template = ""
                for sketch_node in InorderWalk(node.subtrees[1]):
                    if sketch_node.root == "id" or sketch_node.root == "sketch": continue
                    template += sketch_node.root
                    template += " "
                template = template[:-1]
                post_id = node.subtrees[0].subtrees[0].root
                break
    return post_id,template
            

def get_assert_cond(program):
    for word in program.split():
        if word == "assert":
            return program.split("assert")[1].split(";")[0].strip()


def convert_to_z3_expression(py_expression):

    # Split each 'or' token by 'and'
    and_tokens = py_expression.split(' and ')
    stack,rest = and_tokens[0],and_tokens[1:]
    # Initialize an empty list for 'and' conditions in this 'or' token
    # Combine 'and' conditions in this 'or' token using 'And'
    for compare in rest:
        stack = f'And( {stack}, {compare} )'
    
    return f"lambda d: {stack}"

def calucate_P(before_values,program_ast,skatch_found=[False]):
    if program_ast.root == ";":
        after_values = calucate_P(before_values,program_ast.subtrees[0],skatch_found)
        if skatch_found[0]:
            return after_values
        return calucate_P(after_values,program_ast.subtrees[1],skatch_found)
    if program_ast.root == "if":
        condition = program_ast.subtrees[0]
        cond_value = transform_cond(condition,before_values)
        if cond_value:
            return calucate_P(before_values,program_ast.subtrees[1],skatch_found)
        return calucate_P(before_values,program_ast.subtrees[2],skatch_found)
    if program_ast.root == ":=":
        if '??' in program_ast.terminals:
            skatch_found[0]=True
            return before_values
        changed_variable = program_ast.subtrees[0].subtrees[0].root
        after_value = transform_cond(program_ast.subtrees[1],before_values)
        after_values = {key: value for key, value in before_values.items() if key!=changed_variable}
        after_values[changed_variable]=after_value
        return after_values
    if program_ast.root == "skip":
        return before_values.copy()
    if program_ast.root == "while":
        local_before = before_values.copy()
        condition = program_ast.subtrees[0]
        while transform_cond(program_ast.subtrees[1],local_before):
            local_before = calucate_P(local_before,program_ast.subtrees[1],skatch_found)
        return local_before



def calucate_Q_reverse(after_values,program_ast,before_skatch_values,decision=False):
    if program_ast.root == ";":
        before_values = calucate_Q_reverse(after_values,program_ast.subtrees[1],before_skatch_values)
        values = calucate_Q_reverse(before_values,program_ast.subtrees[0],before_skatch_values)
        if values == None : # a decision in subtree 1 is wrong
            before_values = calucate_Q_reverse(after_values,program_ast.subtrees[1],before_skatch_values,True)
            return calucate_Q_reverse(before_values,program_ast.subtrees[0],before_skatch_values)
        else: 
            return values
    if program_ast.root == "if":
        condition = program_ast.subtrees[0]
        then_expr_values = calucate_Q_reverse(after_values,program_ast.subtrees[1],before_skatch_values)
        else_expr_values = calucate_Q_reverse(after_values,program_ast.subtrees[2],before_skatch_values)
        then_cond_value = transform_cond(condition,then_expr_values)
        else_cond_value = transform_cond(condition,else_expr_values)
        if then_cond_value and else_cond_value:
            return then_expr_values
        elif (not then_cond_value) and (not else_cond_value):
            return else_expr_values
        else : # it's a mismatch and we have to choose we choose True
            return then_expr_values if decision else else_expr_values
    if program_ast.root == "while":
        local_after = after_values.copy()
        '''
        we impl :
        while condition do body ->
                        ---- 
        x # of unroll  |   if condition then body else skip
                        ----
        '''
        condition = program_ast.subtrees[0]
        for _ in range(0,4): # number of unrolls 
            condition = program_ast.subtrees[0]
            before_while_check = transform_cond(condition,local_after)
            if (not before_while_check) and decision:
                return local_after    
            body_values = calucate_Q_reverse(local_after,program_ast.subtrees[1],before_skatch_values)
            if transform_cond(condition,body_values):
                local_after = body_values
        return local_after
    
    if program_ast.root == ":=":
        if '??' in program_ast.terminals:
            if sum([1 if after_values[k]!=before_skatch_values[k] else 0 for k in after_values.keys()]) >1 :
                # not good choices 
                return None
            return after_values
        changed_variable = program_ast.subtrees[0].subtrees[0].root
        reversed_value = transform_reverse_cond(program_ast.subtrees[1],after_values)
        before_values = {key: value for key, value in after_values.items() if key!=changed_variable}
        before_values[changed_variable]=reversed_value
        return before_values
    if program_ast.root == "skip":
        return after_values.copy()
        
def run_wp(program,linv,pvars,var_types,P,Q,examples,text_prog,mode,Q_values=None):
    text_prog.insert("end", "Start Running...:\n", "program")
    got_q_values = True
    if Q_values == None:
        got_q_values = False
    if mode == 'ASSERT':
        ast_prog = WhileParser()(program)
        env = mk_env(pvars,var_types)
        env["types"]=var_types
        if ast_prog:
            assert_cond = get_assert_cond(program)
            post_id,templete_prog = get_sketch_program(ast_prog)
            god_program = send_to_synt_assert(assert_cond,post_id,templete_prog,env)
            pattern_to_remove = r"assert \w+ = (\w+ [+\-*/] \w+)( [+\-*/] \w+)*( ;)?"
            program = re.sub(pattern_to_remove, "", program)
    else:
        first_example = True
        god_program = None
        Q_values_store=[]
        ast_prog = WhileParser()(program)
        env = mk_env(pvars,var_types)
        env["types"]=var_types
        for idx,example in enumerate(examples):
            P = example['P']
            Q = example['Q']
            if ast_prog:
                if not got_q_values:
                    Q_values=extract_values_from_Q(example['q_str'],env)
                p_values_till_skatch = calucate_P(extract_values_from_Q(example['p_str'],env),ast_prog)
                new_Q_values = calucate_Q_reverse(Q_values,ast_prog,p_values_till_skatch)
                post_id, _,templete = sketch_verify(P, ast_prog, Q, env,linv=linv,global_env=env)
                Q_values_store.append(new_Q_values)
                if god_program :
                    if not check_aginst_current_program(god_program,Q_values,post_id,env):
                        god_program = send_to_synt_pbe(Q_values_store,post_id,env,templete)
                else:
                    #first check if current god_prog is 
                    god_program = send_to_synt_pbe(Q_values_store,post_id,env,templete)
                
            else:
                print(">> Invalid program.")

    if program.endswith('; '): program = program[-1::-1].replace('; ', '',1)[-1::-1]
    if god_program == None:
        text_prog.insert("end", ">> Synthesizer Do Not Support.\n", "title")
        return
    program = program.replace("??",god_program)
    ast_program = WhileParser()(program)
    text_prog.insert("end", "Verifying the following program:\n", "title")
    text_prog.insert("end",program+"\n", "program")
    text_prog.insert("end","-----------------------------\n", "title")
    if 'p_str' in examples[0]:
        P=eval(convert_to_z3_expression(re.split('lambda \w\: ?', examples[0]['p_str'])[1]))
        Q=eval(convert_to_z3_expression(re.split('lambda \w\: ?', examples[0]['q_str'])[1]))
    verify_env = env.copy()
    del verify_env["types"]
    verify(P, ast_program, Q,pvars, linv=linv,env=verify_env,text_prog=text_prog)
    