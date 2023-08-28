import ast
from z3 import *

# Define a dictionary to map AST operators to Z3 operators
operators = {
    ast.Add: lambda x, y: x + y,
    ast.Sub: lambda x, y: x - y,
    ast.Mult: lambda x, y: x * y,
    ast.Div: lambda x, y: x / y
}

# Define a recursive function to convert the AST to a Z3 formula
def ast_to_z3(node, variables):
    if isinstance(node, ast.Name):
        if node.id in variables:
            return variables[node.id]
        #its a num 
        return Int(node.id)
    elif isinstance(node, ast.BinOp):
        left = ast_to_z3(node.left, variables)
        right = ast_to_z3(node.right, variables)
        operator_func = operators[type(node.op)]
        return operator_func(left, right)
    else:
        #TODO probably raise error and would need to change
        raise ValueError("Unsupported AST node type")

# Example formula string
formula_str = "x + y + num"

# Parse the formula string into an AST
parsed_ast = ast.parse(formula_str, mode='eval')

# Define Z3 variables
x = Int('x')
y = Int('y')
variables = {'x': x, 'y': y}

# Convert the AST to a Z3 formula
z3_formula = ast_to_z3(parsed_ast.body, variables)

print("Z3 Formula:")
print(z3_formula)
