# Define the While language grammar
GRAMMAR = r"""
S   ->   S1     |   S1 ; S
S1  ->   skip   |   id := E   |   if E then S else S1   |   while E do S1
S1  ->   ( S )
E   ->   E0   |   E0 op E0
E0  ->   id   |   num   |   sketch
E0  ->   ( E )
OP ->   +   |   -   |   *   |   /   
"""


import ast
import itertools
from z3 import *
from itertools import product
# Define a dictionary to map AST operators to Z3 operators
operators_old = {
    ast.Add: lambda x, y: x + y,
    ast.Sub: lambda x, y: x - y,
    ast.Mult: lambda x, y: x * y,
    ast.Div: lambda x, y: x / y,
    ast.Eq: lambda x, y: x == y
}
operators_old_2 = {
    "+": lambda x, y: x + y,
    "-": lambda x, y: x - y,
    "*": lambda x, y: x * y,
    "/": lambda x, y: x / y,
    "=": lambda x, y: x == y,
    "concat": lambda x, y: x + y,
    "indexof": lambda x, y: z3.IndexOf(x,y),
    "len": lambda x: z3.Length(x)
}

#? In ASSERRT mode when we called the func ast_to_z3 the op we got was in  ast. foramt so i merge all of them to one dict
operators = {
    "+": lambda x, y: x + y,
    "-": lambda x, y: x - y,
    "*": lambda x, y: x * y,
    "/": lambda x, y: x / y,
    "=": lambda x, y: x == y,
    "concat": lambda x, y: x + y,
    "indexof": lambda x, y: z3.IndexOf(x,y),
    "len": lambda x: z3.Length(x),
    ast.Add: lambda x, y: x + y,
    ast.Sub: lambda x, y: x - y,
    ast.Mult: lambda x, y: x * y,
    ast.Div: lambda x, y: x / y,
    ast.Eq: lambda x, y: x == y
}

def while_tree_to_z3(node, variables):
    if node.root in operators:
        if node.root == "len": # unary
            arg = while_tree_to_z3(node.subtrees[0], variables)
            operator_func = operators[node.root]
            return operator_func(arg)
        else: #binary
            left = while_tree_to_z3(node.subtrees[0], variables)
            right = while_tree_to_z3(node.subtrees[1], variables)
            operator_func = operators[node.root]
            return operator_func(left,right)
    if node.root == 'id':
        return while_tree_to_z3(node.subtrees[0], variables)
    if node.root in variables:
        return variables[node.root]
        #its a num 
    if "num" in node.root :
        return Int(node.root)
    if "string" in node.root:
        return String(node.root)
    print("here")
# Define a recursive function to convert the AST to a Z3 formula
def ast_to_z3(node, variables,free_vars=[]):
    if isinstance(node, ast.Compare):
        left = ast_to_z3(node.left, variables,free_vars)
        right = ast_to_z3(node.comparators[0], variables,free_vars)
        operator_func = operators[type(node.ops[0])]
        return operator_func(left, right)
    if isinstance(node, ast.Name):
        if node.id in variables:
            return variables[node.id]
        #its a num 
        if "num" in node.id :
            free_vars.append(Int(node.id))
            return Int(node.id)
        elif "string" in node.id:
            free_vars.append(String(node.id))
            return String(node.id)
        raise ValueError()
    elif isinstance(node,ast.Constant):
        if type(node.value) == int:
            return IntVal(node.value)
        if type(node.value) == str:
            return StringVal(node.value)
        raise ValueError
    elif isinstance(node, ast.BinOp):
        left = ast_to_z3(node.left, variables,free_vars)
        right = ast_to_z3(node.right, variables,free_vars)
        operator_func = operators[type(node.op)]
        return operator_func(left, right)
    elif isinstance(node,ast.Expression):
        return ast_to_z3(node.body,variables,free_vars)
    #TODO: add section of "Calls" for string operations

count = 0 
# Define some example terminals and non-terminals



# Define a function to generate programs by depth of search
def generate_programs_by_depth(start_symbol, max_depth,grammar_rules,terminals,current_depth=0):
    global count
    if current_depth > max_depth:
        return

    if start_symbol in terminals:
        if start_symbol == "num" or  start_symbol == "string_element":
            count+=1
            yield start_symbol+str(count)
        else:
            yield start_symbol
    else:
        for rule in grammar_rules.get(start_symbol, []):
            tokens = rule.split()
            for expansion in product(*[generate_programs_by_depth(token,  max_depth,grammar_rules,terminals, current_depth + 1) for token in tokens]):
            #for expansion in generate_expansions_by_depth(tokens,max_depth, grammar_rules, terminals, current_depth):
                yield " ".join(expansion)
            # print("debug")

def generate_expansions_by_depth(tokens,max_depth, grammar_rules, terminals, current_depth):
    if not tokens:
        yield []
    else:
        first_token = tokens[0]
        rest_tokens = tokens[1:]
        #for expansion in product(*[generate_programs_by_depth(token,  max_depth,grammar_rules,terminals, current_depth + 1) for token in tokens]):
        for expansion in generate_programs_by_depth(first_token,  max_depth,grammar_rules,terminals, current_depth + 1):
            for rest_expansion in generate_expansions_by_depth(rest_tokens,max_depth, grammar_rules,terminals , current_depth):
                yield [expansion] + rest_expansion
            #yield expansion

# Set the maximum depth you want to generate programs for
max_depth = 4
values = {"a":1,"b":2}
# Start generating programs from the "S" non-terminal with a maximum depth
# for program in generate_programs_by_depth("S", max_depth, values,grammar_rules,):
#     print(program)