
from functools import reduce
from adt.tree import Tree
from parsing.earley.earley import Grammar, Parser, ParseTrees
from parsing.silly import SillyLexer



class LambdaParser(object):

    TOKENS = r"(let|in)(?![\w\d_])   (?P<id>[^\W\d]\w*)   (?P<num>\d+)   [\\.()]".split()
    GRAMMAR = r"""
    E   ->  \.         |   E1  |  E1'
    E1  ->  @          |   E0
    E1' ->  @'         |   E0
    E0  ->  id | num   |  ( E )
    \.  ->  \ L . E 
    @   ->  E1 E0
    @'  ->  E1 \.
    L   ->  id L |
    """

    def __init__(self):
        self.tokenizer = SillyLexer(self.TOKENS)
        self.grammar = Grammar.from_string(self.GRAMMAR)

    def __call__(self, program_text):
        tokens = list(self.tokenizer(program_text))

        earley = Parser(grammar=self.grammar, sentence=tokens, debug=False)
        earley.parse()
        
        if earley.is_valid_sentence():
            trees = ParseTrees(earley)
            assert(len(trees) == 1)
            return self.postprocess(trees.nodes[0])
        else:
            return None
            
    def postprocess(self, t):
        if t.root in ['γ', 'E', 'E0', 'E1', "E1'"] and len(t.subtrees) == 1:
            return self.postprocess(t.subtrees[0])
        elif t.root == 'E0' and t.subtrees[0].root == '(':
            return self.postprocess(t.subtrees[1])
        elif t.root == r'\.':
            args = t.subtrees[1].split()
            t = reduce(lambda t, a: Tree('\\', [a, t]), reversed(args), t.subtrees[3])
        elif t.root == "@'":
            t = Tree('@', t.subtrees)
        elif t.root == 'L':
            t = Tree('.', t.split())

        return Tree(t.root, [self.postprocess(s) for s in t.subtrees])



def pretty(expr):
    if expr.root in ['id', 'num']: return expr.subtrees[0].root
    if expr.root == '\\': return r"(\%s. %s)" % tuple(pretty(s) for s in expr.subtrees)
    elif expr.root == '@': return r"%s %s" % tuple(pretty(s) for s in expr.subtrees)
    else:
        return str(expr)


if __name__ == '__main__':
    
    expr = LambdaParser()(r"\x. x \z g. y 6")
    
    if expr:
        print(">> Valid expression.")
        print(expr)
    else:
        print(">> Invalid expression.")
    
    #s = Sentence([Word("\\", ["\\"]), Word("x", ["id"]), Word(".", ["."])])
    
    