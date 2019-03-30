"""
Lab #2

Your task:
Implement type checking and type inference for simply-typed lambda calculus.
"""

from lambda_calc.syntax import LambdaParser, pretty
from lambda_calc.stdlib import CONSTANTS



def type_inference(expr):
    """
    Input: an expression.
    Output:
     * An annotated expression where every bound variable has a 
       type assignment.
     * The types of free variables occurring in the expression.
     * The type of the expression.
    """



if __name__ == '__main__':
    expr = LambdaParser()(r"""
    let add2 = \x. plus x 2 in
    \f. succ (f True add2)
    """)
    
    if expr:
        print(">> Valid expression.")
        print(pretty(expr))
        type_inference(expr)
    else:
        print(">> Invalid expression.")
