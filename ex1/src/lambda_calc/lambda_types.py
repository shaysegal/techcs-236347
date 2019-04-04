"""
Homework 1

Your task:
Implement type checking and type inference for simply-typed lambda calculus.
"""

from src.lambda_calc.syntax import LambdaParser, pretty
from src.lambda_calc.stdlib import CONSTANTS
from lib.adt.tree import Tree


def type_inference(expr: Tree) -> (Tree, Tree):
    """
    Input: an expression.
    Output (tuple):
     * An annotated expression where every bound variable has a 
       type assignment. Tree
     * If uncountered a unification error raise TypeError('Unification error')
     * If there are insufficient types raise TypeError('insufficient type tags error')
    """
    pass


if __name__ == '__main__':
    expr = LambdaParser()(r"""
    let add2 = \x. plus x 2 in
    \f. succ (f True add2)
    """)
    
    if expr:
        print(">> Valid expression.")
        print(pretty(expr))
        print(type_inference(expr))
        # from lib.adt.tree.viz import dot_print
        # dot_print(expr)
        # dot_print(type_inference(expr)[0])
    else:
        print(">> Invalid expression.")
