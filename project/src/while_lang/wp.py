import sys
from pathlib import Path
import math

path_root = Path(__file__).parents[2]
sys.path.append(str(path_root)+'/lib')
sys.path.append(str(path_root)+'/src')
from lib.adt.tree.walk import PreorderWalk
from while_lang.syntax import WhileParser
import operator
import re
import inspect
from top_down import generate_programs_by_depth
from z3 import Int, ForAll, Implies, Not, And, Or, Solver, unsat, sat
old_prog = None

OP = {'+': operator.add, '-': operator.sub,
      '*': operator.mul, '/': operator.floordiv,
      '!=': operator.ne, '>': operator.gt, '<': operator.lt,
      '<=': operator.le, '>=': operator.ge, '=': operator.eq}

terminals = set(["skip", "num", "+","-","*","/", "sketch", "if", "then", "else", "while", "do", ";",":=", "(", ")"])
non_terminals = set(["S", "S1", "E", "E0"])
grammar_rules = {
    "S": ["S1", "S1 ; S"],
    "S1": ["skip", "id := E", "if E then S else S1", "while E do S1", "( S )"],
    "E": ["E0", "E0 OP E0"],
    "OP": ["+", "-", "*", "/"],
    "E0": [ "num", "sketch", "( E )"]
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
        var,value = re.findall(f'd\[\'[{all_var_regx}]+\'\]==\d+',arg.replace(" ",""))[0].split('==')
        var = var.split('[')[1].strip("]'")
        values[var] = int(value)

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

def send_to_synt(values,post_id):
    global grammar_rules,terminals
    expected_value = values[post_id]
    prog_values  = values.copy()
    del prog_values[post_id]
    grammar_rules['E0'] = list(values.keys()) + grammar_rules['E0']
    terminals.update(values.keys())
    for program in generate_programs_by_depth("E", 5,grammar_rules,terminals):
        # return program
        is_prog_fit = check_current_values_againt_program(program,values,post_id)
        if(is_prog_fit):
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
            if ast.subtrees[1].root == "sketch":
                post_id = ast.subtrees[0].subtrees[0].root
                # P_values = extract_values_from_Q(P,env)
                Q_values = extract_values_from_Q(Q,env)
                # if not first example , check aginst old generated program.
                old_fits = False
                if old_prog != None:
                    old_fits = check_current_values_againt_program(old_prog,Q_values,post_id)
                if old_fits:
                    return old_prog
                prog = send_to_synt(Q_values,post_id)
                old_prog = prog
                return prog
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
if __name__ == '__main__':
    # example program
    #pvars = ['a', 'b', 'i', 'n']
    #program = "a := b ; while i < n do ( a := a + 1 ; b := b + 1 )"
    #P = lambda _: True
    #Q = lambda env: env['a'] == env['b']
    #linv = lambda d: d['a'] == d['b']

    #
    # Following are other programs that you might want to try
    #

    ## Program 1
    # pvars = ['x', 'i', 'y']
    # program = "y := 0 ; while y < i do ( x := x + y ; if (x * y) < 10 then y := y + 1 else skip )"
    # P = lambda d: d['x'] > 0
    # Q = lambda d: d['x'] > 0
    # linv = lambda d: d['y'] >= 0



    ##program scratch
    linv = lambda d: d['y'] >= 0
    pvars = ['a', 'b', 'sum']
    program = """
    sum := ??
    """
    P = lambda d: d['a'] ==3 and d['b'] == 5  and d['sum'] == 0
    Q = lambda d: d['a'] ==3 and d['b'] == 5  and d['sum'] == 8

    ## Program 2
    #pvars = ['a', 'b']
    #program = "while a != b do if a > b then a := a - b else b := b - a"
    #P = lambda d: And(d['a'] > 0, d['b'] > 0)
    #Q = lambda d: And(d['a'] > 0, d['a'] == d['b'])
    #linv = lambda d: ??

    ast = WhileParser()(program)

    if ast:
        print(">> Valid program.")
        # Your task is to implement "verify"
        verify(P, ast, Q, linv=linv)
    else:
        print(">> Invalid program.")

