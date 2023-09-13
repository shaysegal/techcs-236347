import PySimpleGUI as sg
from window import Window
import os
import json
import time
from wp import run_wp
import re
import ast
from collections import OrderedDict
from z3 import Int,String, ForAll, Implies, Not, And, Or, Solver, unsat, sat,Length,Concat,IndexOf


window = Window()
curr_window = window.get_curr_window()

PBE_SIMPLE_DICT = 'examples/pbe_simple/'
PBE_PROGRAM_DICT = 'examples/pbe_program/'
ASSERT_SIMPLE_DICT = 'examples/assert_simple/'
ASSERT_PROGRAM_DICT = 'examples/assert_program/'


def read_jsons_from_dir(directory_path):
    data_dict = {}
    for root, dirs, files in os.walk(directory_path):
        for file in files:
            if file.endswith(".json"):
                file_path = os.path.join(root, file)
                file_name = file.split('.')[0]
            
                with open(file_path, 'r') as json_file:
                    json_data = json.load(json_file)
                    
                    program = json_data['program']
                    linv = json_data['linv']
                    pvars = json_data['pvars']
                    if 'vars_type' in json_data:
                        vars_type = json_data['vars_type']
                    else: vars_type = []
                    P = []
                    Q = []
                    if 'P' in json_data:
                        P = json_data['P']
                        Q = json_data['Q']
                    data_dict[file_name] = {'program': program, 'linv': linv, 'pvars': pvars, 'vars_type': vars_type ,'P': P, 'Q': Q}
    
    data_dict = OrderedDict(sorted(data_dict.items(), key=lambda t: int(re.search(r'\d+', t[0]).group())))
    return data_dict


pbe_simple_dict = read_jsons_from_dir(PBE_SIMPLE_DICT)
pbe_program_dict = read_jsons_from_dir(PBE_PROGRAM_DICT)
assert_simple_dict = read_jsons_from_dir(ASSERT_SIMPLE_DICT)
assert_program_dict = read_jsons_from_dir(ASSERT_PROGRAM_DICT)

working_wp = False



def get_vars_types(examples,pvars):
    expression = re.split('lambda \w\: ?',examples[0]['p_str'])[1]
    lambda_name = re.split('lambda (\w)\: ?',examples[0]['p_str'])[1]
    vars_types = {}
    for var_name in pvars:
        key_to_extract = f"{lambda_name}['{var_name}']"
        match = re.search(fr"{re.escape(key_to_extract)}\s*==\s*'([^']*)'", expression)
        if not match:
            match = re.search(fr"{re.escape(key_to_extract)}\s*==\s*(\d+)", expression)
        try:
            vars_types[var_name] = eval(match.group(1))
        except:
            vars_types[var_name] = match.group(1) 
    for key,var in vars_types.items():
        if isinstance(var,int):
            vars_types[key] = Int
        if isinstance(var,str):
            vars_types[key] = String
    return vars_types

def process_all_inputs(example):
    program = example['program']
    linv = example['linv']
    pvars = example['pvars']
    P = example['P']
    Q = example['Q']
    pvars = eval(pvars)
    linv = eval(linv)
    examples =[]
    for p,q in zip(P,Q):
        example ={}
        example['P'] = eval(p)
        example['p_str'] = p
        example['Q'] = eval(q)
        example['q_str'] = q
        examples.append(example)
    vars_types = get_vars_types(examples,pvars)
    return program,linv,pvars,vars_types,P,Q,examples

def run_pbe_simple_synth():
    global curr_window,text_ex,text_prog,working_wp,pbe_simple_dict
    first_key,example = next(iter(pbe_simple_dict.items()))
    del pbe_simple_dict[first_key]
    print_to_example(first_key,example['program'],example['linv'],example['pvars'],example['P'],example['Q'])
    program,linv,pvars,vars_types,P,Q,examples = process_all_inputs(example)
    run_wp(program,linv,pvars,vars_types,P,Q,examples,text_prog,mode="PBE")
    working_wp = False

def run_pbe_program_synth():
    global curr_window,text_ex,text_prog,working_wp,pbe_program_dict
    first_key = next(iter(pbe_program_dict.keys()))
    example = pbe_program_dict.pop(first_key)
    print_to_example(first_key,example['program'],example['linv'],example['pvars'],example['P'],example['Q'])
    program,linv,pvars,vars_types,P,Q,examples = process_all_inputs(example)
    run_wp(program,linv,pvars,vars_types,P,Q,examples,text_prog,mode="PBE")
    working_wp = False

def run_assert_simple_synth():
    global curr_window,text_ex,text_prog,working_wp,assert_simple_dict
    first_key = next(iter(assert_simple_dict.keys()))
    example = assert_simple_dict.pop(first_key)
    print_to_example(first_key,example['program'],example['linv'],example['pvars'],example['P'],example['Q'])
    program,linv,pvars,vars_types,P,Q,examples = process_all_inputs(example)
    run_wp(program,linv,pvars,vars_types,P,Q,examples,text_prog,mode="ASSERT")
    working_wp = False


def run_assert_program_synth():
    global curr_window,text_ex,text_prog,working_wp,assert_program_dict
    first_key = next(iter(assert_program_dict.keys()))
    example = assert_program_dict.pop(first_key)
    print_to_example(first_key,example['program'],example['linv'],example['pvars'],example['P'],example['Q'])
    program,linv,pvars,vars_types,P,Q,examples = process_all_inputs(example)
    run_wp(program,linv,pvars,vars_types,P,Q,examples,text_prog,mode="ASSERT")
    working_wp = False


def print_to_example(example_no,program,linv,pvars,P,Q):
    global curr_window,text_ex,text_prog
    if example_no != "User Input":
        text_ex.insert("end", "Example No" + example_no.split('_')[1] + ":\n", "title")
    else: text_ex.insert("end", example_no + ":\n", "title")
    text_ex.insert("end", "------------------------\n", "title")
    text_ex.insert("end", "Program: ", "title")
    text_ex.insert("end",program+"\n", "example")
    text_ex.insert("end", "Linv: ", "title")
    text_ex.insert("end",linv+"\n", "example")
    text_ex.insert("end", "Pvars: ", "title")
    text_ex.insert("end",pvars+"\n", "example")
    if P == []:
        return
    if len(P) > 1 and type(P) == list:
        for index, p in enumerate(P):
            text_ex.insert("end", "Input and Output No" + str(index+1) + ":\n", "title") 
            text_ex.insert("end", "P: ", "title")
            text_ex.insert("end", p+"\n", "example")
            text_ex.insert("end", "Q: ", "title")
            text_ex.insert("end", Q[index]+"\n", "example")
            text_ex.insert("end", "------------------------\n", "title")
    else:
        text_ex.insert("end", "Input and Output:\n", "title")
        text_ex.insert("end", "P: ", "title")
        text_ex.insert("end", P[0]+"\n", "example")
        text_ex.insert("end", "Q: ", "title")
        text_ex.insert("end", Q[0]+"\n", "example")


def run(synthesizer_mode):
    global curr_window, working_wp,text_ex,text_prog
    text_ex = curr_window["-OUT_EXAMPLE-"].Widget
    text_ex.tag_config("example", foreground="orange")
    text_ex.tag_config("title", foreground="white")
    text_prog = curr_window["-OUT_PROG-"].Widget
    text_prog.tag_config("program", foreground="cyan")
    text_prog.tag_config("title", foreground="white")
    if not working_wp:
        working_wp = True
        if(synthesizer_mode == 'PBE - Simple'): curr_window.perform_long_operation(lambda: run_pbe_simple_synth(), '-OPERATION DONE-')
        elif(synthesizer_mode == 'PBE - As Part Of Program'): curr_window.perform_long_operation(lambda: run_pbe_program_synth(), '-OPERATION DONE-')
        elif(synthesizer_mode == 'ASSERT - Simple'): curr_window.perform_long_operation(lambda: run_assert_simple_synth(), '-OPERATION DONE-')
        elif(synthesizer_mode == 'ASSERT - As Part Of Program'): curr_window.perform_long_operation(lambda: run_assert_program_synth(), '-OPERATION DONE-')
    else: sg.popup_quick_message("Running right now\nPlease wait until finish running the program",auto_close_duration=3)

def run_pbe_simple_synth_user(program,linv,pvars,vars_types,P,Q,examples,Q_values):
    global text_prog
    run_wp(program,linv,pvars,vars_types,P,Q,examples,text_prog,mode="PBE",Q_values=Q_values)

def run_pbe_program_synth_user(program,linv,pvars,vars_types,P,Q,examples,Q_values):
    global text_prog
    run_wp(program,linv,pvars,vars_types,P,Q,examples,text_prog,mode="PBE",Q_values=Q_values)

def run_assert_simple_synth_user(program,linv,pvars,vars_types,P,Q,examples,Q_values):
    global text_prog
    run_wp(program,linv,pvars,vars_types,P,Q,examples,text_prog,mode="ASSERT",Q_values=Q_values)

def run_assert_program_synth_user(program,linv,pvars,vars_types,P,Q,examples,Q_values):
    global text_prog
    run_wp(program,linv,pvars,vars_types,P,Q,examples,text_prog,mode="ASSERT",Q_values=Q_values)


def make_lambda(str_cond):
    # Define a mapping for comparison operators
    operator_mapping = {
        '<': lambda x, y: x < y,
        '<=': lambda x, y: x <= y,
        '>': lambda x, y: x > y,
        '>=': lambda x, y: x >= y,
        '!=': lambda x, y: x != y,
        '==': lambda x, y: x == y,
    }

    # Parse the string condition into an abstract syntax tree (AST)
    parsed_condition = ast.parse(str_cond, mode='eval').body

    # Define a function to recursively traverse the AST and generate the lambda function
    def generate_lambda(node):
        if isinstance(node, ast.BoolOp):
            op = node.op
            left_lambda = generate_lambda(node.values[0])
            right_lambda = generate_lambda(node.values[1])
            return lambda d: op(left_lambda(d), right_lambda(d))
        elif isinstance(node, ast.Compare):
            left = node.left
            ops = node.ops
            comparators = node.comparators
            assert len(ops) == 1 and len(comparators) == 1
            operator = operator_mapping[ops[0].__class__.__name__]
            left_var = left.id
            right_value = comparators[0].n
            return lambda d: operator(d[left_var], right_value)
        else:
            raise ValueError(f"Unsupported AST node type: {type(node).__name__}")

    # Generate and return the lambda function
    lambda_func = generate_lambda(parsed_condition)
    return lambda_func

def convert_user_input_to_vars_type(pvars,Q):
    vars_types_temp = {}
    vars_types = {}
    expression = Q
    Q_values = {}
    for var_name in pvars:
        pattern = fr"{re.escape(var_name)}\s*==\s*((\d+)|(\w+))"
        match = re.search(pattern, expression)
        value = eval(match.group(1))
        Q_values[var_name] = value
        vars_types_temp[var_name] = value
    for key,var in vars_types_temp.items():
        if isinstance(var,int):
            vars_types[key] = Int
        if isinstance(var,str):
            vars_types[key] = String
    return vars_types, Q_values

def convert_to_z3_expression(py_expression):

    # Split each 'or' token by 'and'
    and_tokens = py_expression.split(' and ')
    stack,rest = and_tokens[0],and_tokens[1:]
    # Initialize an empty list for 'and' conditions in this 'or' token
    # Combine 'and' conditions in this 'or' token using 'And'
    for compare in rest:
        stack = f'And( {stack}, {compare} )'
    
    return f"lambda d: {stack}"

def convert_user_input_to_examples(P,Q,pvars):
    pass

def process_user_mode_input(program,linv,pvars,P,Q):
    #TODO need to implement for long programs
    # program = program.replace("\n","")
    examples = []
    example = {}
    pvars=eval(pvars)
    vars_types,Q_values = convert_user_input_to_vars_type(pvars,Q)
    
    for v in pvars:
        v_to_replace = re.findall(f'{v}\s*[<>=!]+',linv)
        if len(v_to_replace):
            v_to_replace = v_to_replace[0]
            linv = linv.replace(v_to_replace,v_to_replace.replace(v,f"d['{v}']"))
        v_to_replace = re.findall(f'{v}\s*[<>=!]+',P)
        if len(v_to_replace):
            v_to_replace = v_to_replace[0]
            P = P.replace(v_to_replace,v_to_replace.replace(v,f"d['{v}']"))
        v_to_replace = re.findall(f'{v}\s*[<>=!]+',Q)
        if len(v_to_replace):
            v_to_replace = v_to_replace[0]
            Q =  Q.replace(v_to_replace,v_to_replace.replace(v,f"d['{v}']"))
    linv=eval(convert_to_z3_expression(linv))
    P=eval(convert_to_z3_expression(P))
    Q=eval(convert_to_z3_expression(Q))
    example['P'] = P
    example['Q'] = Q
    examples.append(example)
    return program,linv,pvars,vars_types,P,Q,examples,Q_values

def run_user_synth(program,linv,pvars,P,Q,synthesizer_mode):
    global curr_window, working_wp,text_ex,text_prog
    text_ex = curr_window["-INPUT_PROG-"].Widget
    text_ex.tag_config("example", foreground="orange")
    text_ex.tag_config("title", foreground="white")
    text_prog = curr_window["-OUT_PROG-"].Widget
    text_prog.tag_config("program", foreground="cyan")
    text_prog.tag_config("title", foreground="white")
    program,linv,pvars,vars_types,P,Q, examples,Q_values= process_user_mode_input(program,linv,pvars,P,Q)
    if not working_wp:
        working_wp = True
        if(synthesizer_mode == 'PBE - Simple'): curr_window.perform_long_operation(lambda: run_pbe_simple_synth_user(program,linv,pvars,vars_types,P,Q,examples,Q_values), '-OPERATION DONE-')
        elif(synthesizer_mode == 'PBE - As Part Of Program'): curr_window.perform_long_operation(lambda: run_pbe_program_synth_user(program,linv,pvars,vars_types,P,Q,examples,Q_values), '-OPERATION DONE-')
        elif(synthesizer_mode == 'ASSERT - Simple'): curr_window.perform_long_operation(lambda: run_assert_simple_synth_user(program,linv,pvars,vars_types,P,Q,examples,Q_values), '-OPERATION DONE-')
        elif(synthesizer_mode == 'ASSERT - As Part Of Program'): curr_window.perform_long_operation(lambda: run_assert_program_synth_user(program,linv,pvars,vars_types,P,Q,examples,Q_values), '-OPERATION DONE-')
    else: sg.popup_quick_message("Running right now\nPlease wait until finish running the program",auto_close_duration=3)
    # print_to_example("User Input",program,linv,pvars,P,Q)
    # run_wp(program,linv,pvars,vars_type,P,Q,text_prog,mode="PBE")

def check_input(program,linv,pvars,P,Q):
    if program == "" or linv == "" or pvars == "" or P == "" or Q == "": return True
    try: eval(pvars)
    except: return True
    if type(eval(pvars)) != list: return True
    # if type(eval(P)) != list or type(eval(Q)) != list: return True
    return False

def process_user_input():
    global window,curr_window,working_wp
   
    event, values = curr_window.read()
    while not (event == sg.WIN_CLOSED or event=="Exit"):
        if event == "Go":
            synthesizer_mode = values["-SYNTH_MODE-"]
            run(synthesizer_mode)
        elif event == "Next Example":
            if not working_wp:
                synthesizer_mode = values["-SYNTH_MODE-"]
                curr_window["-OUT_EXAMPLE-"].update("")
                curr_window["-OUT_PROG-"].update("")
                run(synthesizer_mode)
            else: sg.popup_quick_message("Running right now\nPlease wait until finish running the program",auto_close_duration=3)
        elif event == "Run Through Examples":
            curr_window.close()
            curr_window = window.set_layout(window.get_examples_layout())
        elif event == "User Input":
            curr_window.close()
            curr_window = window.set_layout(window.get_user_layout())
        elif event == "Synth Program":
            if not working_wp:
                synthesizer_mode = values["-SYNTH_MODE-"]
                program = values["-INPUT_PROG-"]
                linv = values["-LINV-"]
                pvars = values["-PVARS-"]
                P = values["-P-"]
                Q = values["-Q-"]
                # vars_type = values["-VARS_TYPE-"]
                if check_input(program,linv,pvars,P,Q):
                    sg.popup_quick_message("Input Error!\nPlease read again the Documentation and try again",auto_close_duration=4)
                else:
                    run_user_synth(program,linv,pvars,P,Q,synthesizer_mode)
            else: sg.popup_quick_message("Running right now\nPlease wait until finish running the program",auto_close_duration=3)
        elif event == "Reset ALL":
            curr_window["-INPUT_PROG-"].update("")
            curr_window["-OUT_PROG-"].update("")
            curr_window["-LINV-"].update("")
            curr_window["-PVARS-"].update("")
            curr_window["-P-"].update("")
            curr_window["-Q-"].update("")
        elif event == "Reset":
            curr_window["-INPUT_PROG-"].update("")
            curr_window["-OUT_PROG-"].update("")
        elif event == "Documentation":
            curr_window.close()
            curr_window = window.set_layout(window.get_documentation_layout())
            # curr_window["-DOCS-"].update(window.get_documentation_text())

        elif event == "Main Menu":
            curr_window.close()
            curr_window = window.set_layout(window.get_main_layout())
                
        event, values = curr_window.read()
    curr_window.close()

if __name__ == '__main__':
    process_user_input()