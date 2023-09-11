import PySimpleGUI as sg
from window import Window
import os
import json
import time
from wp import run_wp

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
    
    return data_dict


pbe_simple_dict = read_jsons_from_dir(PBE_SIMPLE_DICT)
pbe_program_dict = read_jsons_from_dir(PBE_PROGRAM_DICT)
assert_simple_dict = read_jsons_from_dir(ASSERT_SIMPLE_DICT)
assert_program_dict = read_jsons_from_dir(ASSERT_PROGRAM_DICT)

working_wp = False


def run_pbe_simple_synth():
    global curr_window,text_ex,text_prog,working_wp,pbe_simple_dict
    first_key = next(iter(pbe_simple_dict.keys()))
    example = pbe_simple_dict.pop(first_key)
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
    
def run_user_synth(program,linv,pvars,P,Q,synthesizer_mode):
    global curr_window, working_wp,text_ex,text_prog
    text_ex = curr_window["-INPUT_PROG-"].Widget
    text_ex.tag_config("example", foreground="orange")
    text_ex.tag_config("title", foreground="white")
    text_prog = curr_window["-OUT_PROG-"].Widget
    text_prog.tag_config("program", foreground="cyan")
    text_prog.tag_config("title", foreground="white")
    if not working_wp:
        working_wp = True
        if(synthesizer_mode == 'PBE - Simple'): curr_window.perform_long_operation(lambda: run_pbe_simple_synth_user(program,linv,pvars,P,Q), '-OPERATION DONE-')
        elif(synthesizer_mode == 'PBE - As Part Of Program'): curr_window.perform_long_operation(lambda: run_pbe_simple_synth_user(program,linv,pvars,P,Q), '-OPERATION DONE-')
        elif(synthesizer_mode == 'ASSERT - Simple'): curr_window.perform_long_operation(lambda: run_pbe_simple_synth_user(program,linv,pvars,P,Q), '-OPERATION DONE-')
        elif(synthesizer_mode == 'ASSERT - As Part Of Program'): curr_window.perform_long_operation(lambda: run_pbe_simple_synth_user(program,linv,pvars,P,Q), '-OPERATION DONE-')
    else: sg.popup_quick_message("Running right now\nPlease wait until finish running the program",auto_close_duration=3)
    print_to_example("User Input",program,linv,pvars,P,Q)
    # run_wp(program,linv,pvars,vars_type,P,Q,text_prog,mode="PBE")


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
                synthesizer_mode = values["-SYNTH_MODE-"]
            else: sg.popup_quick_message("Running right now\nPlease wait until finish running the program",auto_close_duration=3)
        elif event == "Run Through Examples":
            curr_window.close()
            curr_window = window.set_layout(window.get_examples_layout())
        elif event == "User Input":
            curr_window.close()
            curr_window = window.set_layout(window.get_user_layout())
        elif event == "Synth Program":
            synthesizer_mode = values["-SYNTH_MODE-"]
            program = values["-INPUT_PROG-"]
            linv = values["-LINV-"]
            pvars = values["-PVARS-"]
            P = values["-P-"]
            Q = values["-Q-"]
            # vars_type = values["-VARS_TYPE-"]
            if program == "" or linv == "" or pvars == "" or P == "" or Q == "":
                sg.popup_quick_message("Please fill all the fields",auto_close_duration=3)
            else:
                run_user_synth(program,linv,pvars,P,Q,synthesizer_mode)
        elif event == "Documentation":
            curr_window.close()
            curr_window = window.set_layout(window.get_documentation_layout())

        elif event == "Main Menu":
            curr_window.close()
            curr_window = window.set_layout(window.get_main_layout())
                
        event, values = curr_window.read()
    curr_window.close()

if __name__ == '__main__':
    process_user_input()