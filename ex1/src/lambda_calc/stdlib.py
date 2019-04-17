from src.lambda_calc.syntax import LambdaParser


DECLARATIONS = """
    \(succ prev : int -> int) (plus mult pow minus : int -> int -> int)
     (True False : bool) (not : bool -> bool) (and or xor : bool -> bool -> bool)
     (is_zero : int -> bool)
    . dummy
"""


CONSTANTS = {decl.subtrees[0].subtrees[0].root: decl.subtrees[1] 
             for decl in LambdaParser()(DECLARATIONS).split()
             if decl.root == ':'}
