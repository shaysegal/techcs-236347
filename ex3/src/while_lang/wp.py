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

def verify(P, ast, Q):
    """
    Verifies a Hoare triple {P} c {Q}
    Where P, Q are assertions (see below for examples)
    and ast is the AST of the command c.
    """

    print(ast)
    # ...




if __name__ == '__main__':
    # example program
    pvars = ['a', 'b', 'i', 'n']
    program = "a := b ; while i < n do ( a := a + 1 ; b := b + 1 )"    
    P = lambda _: True
    Q = lambda d: d['a'] == d['b']
    linv = lambda d: d['a'] == d['b']
    
    #
    # Following are other programs that you might want to try
    #

    ## Program 1        
    #pvars = ['x', 'i', 'y']
    #program = "y := 0 ; while y < i do ( x := x + y ; if (x * y) < 10 then y := y + 1 else skip )"
    #P = lambda d: d['x'] > 0
    #Q = lambda d: d['x'] > 0
    #linv = lambda d: **figure it out!**

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
        verify(P, ast, Q)
    else:
        print(">> Invalid program.")

