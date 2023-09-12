import PySimpleGUI as sg
from window import Window
import os
import json
import time
from wp import run_wp
import re
import ast
from collections import OrderedDict

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
                    vars_type = json_data['vars_type']
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


def run_pbe_simple_synth():
    global curr_window,text_ex,text_prog,working_wp,pbe_simple_dict
    first_key,example = next(iter(pbe_simple_dict.items()))
    del pbe_simple_dict[first_key]
    # example = pbe_simple_dict.pop(first_key)
    program = example['program']
    linv = example['linv']
    pvars = example['pvars']
    P = example['P']
    Q = example['Q']
    vars_type = example['vars_type']
    print_to_example(first_key,program,linv,pvars,P,Q)
    run_wp(program,linv,pvars,vars_type,P,Q,text_prog,mode="PBE")
    working_wp = False

def run_pbe_program_synth():
    global curr_window,text_ex,text_prog,working_wp,pbe_program_dict
    first_key = next(iter(pbe_program_dict.keys()))
    example = pbe_program_dict.pop(first_key)
    program = example['program']
    linv = example['linv']
    pvars = example['pvars']
    P = example['P']
    Q = example['Q']
    vars_type = example['vars_type']
    print_to_example(first_key,program,linv,pvars,P,Q)
    run_wp(program,linv,pvars,vars_type,P,Q,text_prog,mode="PBE")
    working_wp = False

def run_assert_simple_synth():
    global curr_window,text_ex,text_prog,working_wp,assert_simple_dict
    first_key = next(iter(assert_simple_dict.keys()))
    example = assert_simple_dict.pop(first_key)
    program = example['program']
    linv = example['linv']
    pvars = example['pvars']
    vars_type = example['vars_type']
    print_to_example(first_key,program,linv,pvars,[],[])
    run_wp(program,linv,pvars,vars_type,[],[],text_prog,mode="ASSERT")
    working_wp = False


def run_assert_program_synth():
    global curr_window,text_ex,text_prog,working_wp,assert_program_dict
    first_key = next(iter(assert_program_dict.keys()))
    example = assert_program_dict.pop(first_key)
    program = example['program']
    linv = example['linv']
    pvars = example['pvars']
    vars_type = example['vars_type']
    print_to_example(first_key,program,linv,pvars,[],[])
    run_wp(program,linv,pvars,vars_type,[],[],text_prog,mode="ASSERT")
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

def run_pbe_simple_synth_user(program,linv,pvars,P,Q):
    run_wp(program,linv,pvars,[],P,Q,text_prog,mode="PBE")
def run_pbe_program_synth_user(program,linv,pvars,P,Q):
    run_wp(program,linv,pvars,[],P,Q,text_prog,mode="PBE")
def run_assert_simple_synth_user(program,linv,pvars,P,Q):
    run_wp(program,linv,pvars,[],[],text_prog,mode="ASSERT")
def run_assert_program_synth_user(program,linv,pvars,P,Q):
    run_wp(program,linv,pvars,[],[],text_prog,mode="ASSERT")


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

def process_input(program,linv,pvars,P,Q):
    #TODO need to implement
    raise NotImplemented
    return program,linv,pvars,P,Q

def run_user_synth(program,linv,pvars,P,Q,synthesizer_mode):
    global curr_window, working_wp,text_ex,text_prog
    text_ex = curr_window["-INPUT_PROG-"].Widget
    text_ex.tag_config("example", foreground="orange")
    text_ex.tag_config("title", foreground="white")
    text_prog = curr_window["-OUT_PROG-"].Widget
    text_prog.tag_config("program", foreground="cyan")
    text_prog.tag_config("title", foreground="white")
    program,linv,pvars,P,Q = process_input(program,linv,pvars,P,Q)
    if not working_wp:
        working_wp = True
        if(synthesizer_mode == 'PBE - Simple'): curr_window.perform_long_operation(lambda: run_pbe_simple_synth_user(program,linv,pvars,P,Q), '-OPERATION DONE-')
        elif(synthesizer_mode == 'PBE - As Part Of Program'): curr_window.perform_long_operation(lambda: run_pbe_simple_synth_user(program,linv,pvars,P,Q), '-OPERATION DONE-')
        elif(synthesizer_mode == 'ASSERT - Simple'): curr_window.perform_long_operation(lambda: run_pbe_simple_synth_user(program,linv,pvars,P,Q), '-OPERATION DONE-')
        elif(synthesizer_mode == 'ASSERT - As Part Of Program'): curr_window.perform_long_operation(lambda: run_pbe_simple_synth_user(program,linv,pvars,P,Q), '-OPERATION DONE-')
    else: sg.popup_quick_message("Running right now\nPlease wait until finish running the program",auto_close_duration=3)
    print_to_example("User Input",program,linv,pvars,P,Q)
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