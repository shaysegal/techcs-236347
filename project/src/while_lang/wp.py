import sys
from pathlib import Path
import math
import ast
path_root = Path(__file__).parents[2]
sys.path.append(str(path_root)+'/lib')
sys.path.append(str(path_root)+'/src')
from adt.tree.walk import PreorderWalk
from while_lang.syntax import WhileParser
import operator
import re
import inspect
from top_down import generate_programs_by_depth,ast_to_z3
from z3 import Int,String, ForAll, Implies, Not, And, Or, Solver, unsat, sat,Length,Concat,IndexOf
import z3
old_prog = None

OP = {'+': operator.add, '-': operator.sub,
      '*': operator.mul, '/': operator.floordiv,
      '!=': operator.ne, '>': operator.gt, '<': operator.lt,
      '<=': operator.le, '>=': operator.ge, '=': operator.eq}
STRING_OP = {
    'len':Length,#UnaryOP, might need something else - also - return int and not string
    '++':Concat,
    "indexOf":IndexOf #return int and not string
}
terminals = set(["skip","string_element", "num", "+", "-", "*", "/", "if", "then", "else", "while", "do", ";",":=", "(", ")"])
non_terminals = set(["S", "S1", "E", "E_num","E_string"])
grammar_rules = {
    "S": ["S1", "S1 ; S"],
    "S1": ["skip", "id := E", "if E then S else S1", "while E do S1", "( S )"],
    "E": ["E_num", "E_num OP E_num"," E_string","E_string OP_STRING E_string","UNARY_STRING_OP E_string"],
    "OP": ["+", "-", "*", "/"],
    "OP_STRING":["++","IndexOf"],
    "UNARY_STRING_OP":["Len"],
    "E_num": [ "num", "( E )"],
    "E_string": [ "string_element", "( E )"]
}

def mk_env(pvars):
    return {v : Int(v) for v in pvars}


def upd(env, v, expr):
    env = env.copy()
    env[v] = expr
    return env

def transform_cond(cond,OP,env):
    #should transfrom string to Z3 formual using OP dictionary   
    for node in PreorderWalk(cond):
        if node.root in OP:
            return OP[node.root](transform_cond(node.subtrees[0], OP, env),transform_cond(node.subtrees[1], OP, env))
        else:
            return env[node.subtrees[0].root] if node.subtrees[0].root in env else node.subtrees[0].root
def extract_values_from_Q(Q,env):
    # raise NotImplemented
    values = {}
    # values.update(env)
    # result = P(env)
    all_var_regx = "|".join(env.keys())
    for arg in inspect.getsource(Q).split('and'):
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

def send_to_synt(values_array,post_id,env):
    global grammar_rules,terminals
    var_types = env["types"]
    expected_value = values_array[0][post_id]
    prog_values  = values_array[0].copy()
    del prog_values[post_id]
    for var in values_array[0].keys():
        if var_types[var] == Int :
            grammar_rules['E_num'] = [var]+ grammar_rules['E_num']
            continue
        if var_types[var] == String :
            grammar_rules['E_string'] = [var]+ grammar_rules['E_string']
            continue
        raise ValueError()
    
    terminals.update(prog_values.keys())
    for program in generate_programs_by_depth("E", 5,grammar_rules,terminals):
        print("debug program",program)
        sol = Solver()
        should_check=True
        for example_number,values in enumerate(values_array):
            expected_value = values[post_id]
            z3_lut={}
            for k in values.keys():
                z3_type_ctor=var_types[k]
                z3_lut[k]=z3_type_ctor(k+str(example_number))
            try:
                z3_prog = ast_to_z3(ast.parse(program,mode='eval'),z3_lut)
            except Exception as e:
                print("z3 Error")
                should_check=False
                break
            formula = None
            try:
                formula = operator.eq(z3_prog,expected_value)
            except Exception as e:
                print("z3 Error")
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
    # if(prog == None):
    #     raise Exception("No program found")
    # return prog

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

            if ast.subtrees[1].root == "sketch": # TODO: doest this still necesery ? 
                post_id = ast.subtrees[0].subtrees[0].root
                # P_values = extract_values_from_Q(P,env)
                Q_values = extract_values_from_Q(Q,env) 
                # if not first example , check aginst old generated program.
                old_fits = False
                if old_prog != None:
                    old_fits = check_current_values_againt_program(old_prog,Q_values,post_id)
                if old_fits:
                    return old_prog
                working_prog = send_to_synt(Q_values,post_id,env)
                old_prog = working_prog
                return working_prog
            #    P,Q
            #    P-> values of variable.
            #    sketch -> function that i create 
            #    for P,Q in [Ps,Qs]
            #    And( P Implies sketch(p)=Q)
            #    prog = send_to_synt(Ps,Qs)
            #    return prog
            v,expr = ast.subtrees
            e_at_x = upd(env,str(transform_cond(v,OP,env)),transform_cond(expr,OP,env))
            return Q(e_at_x)
            #something with z3
        case "while":

            P = linv
            b , c = ast.subtrees
            b = transform_cond(b,OP, global_env)

            return And(P(env),
                       ForAll(list(global_env.values()),                  
                              And(
                                Implies(
                                    And(P(global_env),b),
                                        inner_verify(P,c,linv,global_env.copy(),linv,global_env)),
                                Implies(
                                    And(P(global_env),Not(b)),
                                        Q(global_env))
                                  )
                                )
                        )


        case "if":    

            b ,c_1,c_2 = ast.subtrees
            b = transform_cond(b,OP, env)
            return Or(And(b,inner_verify(P,c_1,Q,env,linv,global_env)),And(Not(b),inner_verify(P,c_2,Q,env,linv,global_env)))
        case "skip":    
            return Q(env)
    return 

def sketch_verify(P, ast, Q, env ,linv,global_env):
    global old_prog
    match ast.root :
        case ";":
            #seq 
            #M=None
            #inner_lambda = inner_verify(P,ast.subtrees[1],Q,env,linv)
            wp_c2=lambda new_env : inner_verify(P,ast.subtrees[1],Q,new_env.copy(),linv,global_env) #TODO: potential BUG - call to inner verify instead of sketch verfiy 
            return inner_verify(P,ast.subtrees[0],wp_c2,env,linv,global_env)
        case ":=":
            #assign
            if ast.subtrees[1].root == "sketch":
                post_id = ast.subtrees[0].subtrees[0].root
                Q_values = extract_values_from_Q(Q,env)
                return post_id, Q_values
            #    P,Q
            #    P-> values of variable.
            #    sketch -> function that i create 
            #    for P,Q in [Ps,Qs]
            #    And( P Implies sketch(p)=Q)
            #    prog = send_to_synt(Ps,Qs)
            #    return prog
            v,expr = ast.subtrees
            e_at_x = upd(env,str(transform_cond(v,OP,env)),transform_cond(expr,OP,env))
            return Q(e_at_x)
            #something with z3
        case "while":

            P = linv
            b , c = ast.subtrees
            b = transform_cond(b,OP, global_env)

            return And(P(env),
                       ForAll(list(global_env.values()),                  
                              And(
                                Implies(
                                    And(P(global_env),b),
                                        inner_verify(P,c,linv,global_env.copy(),linv,global_env)),
                                Implies(
                                    And(P(global_env),Not(b)),
                                        Q(global_env))
                                  )
                                )
                        )


        case "if":    

            b ,c_1,c_2 = ast.subtrees
            b = transform_cond(b,OP, env)
            return Or(And(b,inner_verify(P,c_1,Q,env,linv,global_env)),And(Not(b),inner_verify(P,c_2,Q,env,linv,global_env)))
        case "skip":    
            return Q(env)
    return 



def verify(P, ast, Q, linv=None):
    """
    Verifies a Hoare triple {P} c {Q}
    Where P, Q are assertions (see below for examples)
    and ast is the AST of the command c.
    Returns `True` iff the triple is valid.
    Also prints the counterexample (model) returned from Z3 in case
    it is not.
    """
    #P,Q
    pvars = ['a','b','sum']#set(filter(lambda t: type(t) == str and t!='skip' ,ast.terminals))
    env = mk_env(pvars)
    ret = inner_verify(P, ast, Q, env.copy(),linv,env.copy())
    sol = Solver()
    formula = Implies(P(env),ret)
    sol.add(Not(formula))
    status = sol.check()
    if status == sat:
        m = sol.model()
        return False , m
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
        


if __name__ == '__main__':
    program =  "sum := ??"
    linv = lambda d: d['y'] >= 0
    pvars = ['a', 'b', 'sum']
    #var_types={
    #    'a':Int,
    #    'b':Int,
    #    'sum':Int
    #}
    var_types={
        'a':String,
        'b':String,
        'sum':String
    }
    examples =[]
    example1 = {}
    #example1['P'] = lambda d: d['a'] == 3 and d['b'] == 4 and d['sum'] == 0
    #example1['Q'] = lambda d: d['a'] == 3 and d['b'] == 4 and d['sum'] == 12
    example1['P'] = lambda d: d['a'] == 'abc' and d['b'] == 'aaa' and d['sum'] == ''
    example1['Q'] = lambda d: d['a'] == 'abc' and d['b'] == 'aaa' and d['sum'] == 'abcaaa'
    examples.append(example1)
    example2 = {}
    #example2['P'] = lambda d: d['a'] == 5 and d['b'] == 2 and d['sum'] == 0
    #example2['Q'] = lambda d: d['a'] == 5 and d['b'] == 2 and d['sum'] == 10
    example2['P'] = lambda d: d['a'] == 'abc' and d['b'] == 'bab' and d['sum'] == ''
    example2['Q'] = lambda d: d['a'] == 'abc' and d['b'] == 'bab' and d['sum'] == 'abcbab'
    examples.append(example2) 
    # find god_program
    first_example = True
    god_program = None
    Q_values_store=[]
    for idx,example in enumerate(examples):
        P = example['P']
        Q = example['Q']
        ast_prog = WhileParser()(program)
        env = mk_env(pvars)
        env["types"]=var_types
        if ast_prog:
            post_id, Q_values = sketch_verify(P, ast_prog, Q, env,linv=linv,global_env=env)
            Q_values_store.append(Q_values)
            if god_program :
                if not check_aginst_current_program(god_program,Q_values,post_id,env):
                    god_program = send_to_synt(Q_values_store,post_id,env)
            else:
                #first check if current god_prog is 
                god_program = send_to_synt(Q_values_store,post_id,env)
            

        else:
            print(">> Invalid program.")

    program = program.replace("??",god_program)
    ast_program = WhileParser()(program)
    # final verify
    verify(P, ast_program, Q, linv=linv)

