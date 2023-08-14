import sys
from pathlib import Path

path_root = Path(__file__).parents[2]
sys.path.append(str(path_root)+'/lib')
sys.path.append(str(path_root)+'/src')

from while_lang.syntax import WhileParser
import operator
from z3 import Int, ForAll, Implies, Not, And, Or, Solver, unsat, sat

OP = {'+': operator.add, '-': operator.sub,
      '*': operator.mul, '/': operator.floordiv,
      '!=': operator.ne, '>': operator.gt, '<': operator.lt,
      '<=': operator.le, '>=': operator.ge, '=': operator.eq}


def mk_env(pvars):
    return {v : Int(v) for v in pvars}


def upd(d, k, v):
    d = d.copy()
    d[k] = v
    return d


def recursive_pvars(ast):
    if ast.root == 'id':
        return [ast.subtrees[0].root]

    if ast.root == ':=':
        return [ast.subtrees[0].subtrees[0].root] + recursive_pvars(ast.subtrees[1])

    if ast.root in [';', 'while'] or ast.root in OP.keys():
        return recursive_pvars(ast.subtrees[0]) + recursive_pvars(ast.subtrees[1])

    if ast.root == 'if':
        return (recursive_pvars(ast.subtrees[0]) + recursive_pvars(ast.subtrees[1]) +
                recursive_pvars(ast.subtrees[2]))

    return []  # invalid case


def exp_val(ast, env):
    if ast.root == 'id':
        return env[ast.subtrees[0].root]

    if ast.root == 'num':
        return ast.subtrees[0].root

    if ast.root in OP.keys():
        return OP[ast.root](exp_val(ast.subtrees[0], env), exp_val(ast.subtrees[1], env))

    print('error calculating value')
    return None


def lambda_wp(ast, Q, linv, pvars):
    if ast.root == ':=':
        return lambda env: Q(upd(env, ast.subtrees[0].subtrees[0].root, exp_val(ast.subtrees[1], env)))

    if ast.root == ';':
        wp_r = lambda_wp(ast.subtrees[1], Q, linv, pvars)
        return lambda_wp(ast.subtrees[0], wp_r, linv, pvars)

    if ast.root == 'if':
        return lambda e: Or(And(lambda_wp(ast.subtrees[1], Q, linv, pvars)(e), exp_val(ast.subtrees[0], e)),
                            And(lambda_wp(ast.subtrees[2], Q, linv, pvars)(e), Not(exp_val(ast.subtrees[0], e))))

    if ast.root == 'while':
        env = mk_env(pvars)
        return lambda e: And(linv(e),  # Sorry for the horrible indentation, pycharm stuff...
                             ForAll([val for val in env.values()],
                                    And(Implies(And(linv(env), exp_val(ast.subtrees[0], env)),
                                                lambda_wp(ast.subtrees[1], linv, None, pvars)(env)),
                                        Implies(And(linv(env), Not(exp_val(ast.subtrees[0], env))), Q(env)))))
    return Q


def verify(P, ast, Q, linv=None):
    """
    Verifies a Hoare triple {P} c {Q}
    Where P, Q are assertions (see below for examples)
    and ast is the AST of the command c.
    Returns `True` iff the triple is valid.
    Also prints the counterexample (model) returned from Z3 in case
    it is not.
    """

    print(ast)
    pvars = list(set(recursive_pvars(ast)))
    env = mk_env(pvars)
    wp = lambda_wp(ast, Q, linv, pvars)
    z3_solver = Solver()
    z3_solver.add(Not(Implies(P(env), wp(env))))
    if z3_solver.check() == sat:
        print(z3_solver.model)
        return False
    return True


if __name__ == '__main__':
    # example program
    #pvars = ['a', 'b', 'i', 'n']
    #program = "a := b ; while i < n do ( a := a + 1 ; b := b + 1 )"
    #P = lambda _: True
    #Q = lambda d: d['a'] == d['b']
    #linv = lambda d: d['a'] == d['b']

    #
    # Following are other programs that you might want to try
    #

    ## Program 1
    pvars = ['x', 'i', 'y']
    program = "y := ?? ; while y < i do ( x := x + y ; if (x * y) < 10 then y := y + 1 else skip )"
    P = lambda d: d['x'] > 0
    Q = lambda d: d['x'] > 0
    linv = lambda d: d['y'] >= 0

    ## Program 2
    #pvars = ['a', 'b']
    #program = "while a != b do if a > b then a := a - b else b := b - a"
    #P = lambda d: And(d['a'] > 0, d['b'] > 0)
    #Q = lambda d: And(d['a'] > 0, d['a'] == d['b'])
    #linv = lambda d: ???

    ast = WhileParser()(program)

    if ast:
        print(">> Valid program.")
        # Your task is to implement "verify"
        verify(P, ast, Q, linv=linv)
    else:
        print(">> Invalid program.")

