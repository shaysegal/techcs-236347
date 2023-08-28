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

# Define some example terminals and non-terminals

# Define a function to generate programs by depth of search
def generate_programs_by_depth(start_symbol, max_depth,grammar_rules,terminals,current_depth=0):
    if current_depth > max_depth:
        return

    if start_symbol in terminals:
        yield start_symbol
    else:
        for rule in grammar_rules.get(start_symbol, []):
            tokens = rule.split()
            for expansion in generate_expansions_by_depth(tokens,max_depth, grammar_rules, terminals, current_depth):
                yield " ".join(expansion)

def generate_expansions_by_depth(tokens,max_depth, grammar_rules, terminals, current_depth):
    if not tokens:
        yield []
    else:
        first_token = tokens[0]
        rest_tokens = tokens[1:]
        for expansion in generate_programs_by_depth(first_token,  max_depth,grammar_rules,terminals, current_depth + 1):
            for rest_expansion in generate_expansions_by_depth(rest_tokens,max_depth, grammar_rules,terminals , current_depth):
                yield [expansion] + rest_expansion

# Set the maximum depth you want to generate programs for
max_depth = 4
values = {"a":1,"b":2}
# Start generating programs from the "S" non-terminal with a maximum depth
# for program in generate_programs_by_depth("S", max_depth, values,grammar_rules,):
#     print(program)