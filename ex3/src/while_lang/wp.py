import sys
from pathlib import Path
import math

path_root = Path(__file__).parents[2]
sys.path.append(str(path_root)+'/lib')
sys.path.append(str(path_root)+'/src')
from adt.tree.walk import PreorderWalk
from while_lang.syntax import WhileParser
import operator
from z3 import Int, ForAll, Implies, Not, And, Or, Solver, unsat, sat


OP = {'+': operator.add, '-': operator.sub,
      '*': operator.mul, '/': operator.floordiv,
      '!=': operator.ne, '>': operator.gt, '<': operator.lt,
      '<=': operator.le, '>=': operator.ge, '=': operator.eq}


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


def inner_verify(P, ast, Q, env ,linv,global_env):
    
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
    pvars = set(filter(lambda t: type(t) == str and t!='skip' ,ast.terminals))
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
    pvars = ['x', 'i', 'y']
    program = "y := 0 ; while y < i do ( x := x + y ; if (x * y) < 10 then y := y + 1 else skip )"
    P = lambda d: d['x'] > 0
    Q = lambda d: d['x'] > 0
    linv = lambda d: d['y'] >= 0

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

