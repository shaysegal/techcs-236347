from .syntax import LambdaParser


DECLARATIONS = r"""
    \(succ prev : nat -> nat) (plus mult pow minus : nat -> nat -> nat)
     (True False : bool) (not : bool -> bool) (and or xor : bool -> bool -> bool)
     (is_zero : nat -> bool)
    . dummy
"""


CONSTANTS = {decl.subtrees[0].subtrees[0].root: decl.subtrees[1] 
             for decl in LambdaParser()(DECLARATIONS).split()
             if decl.root == ':'}
