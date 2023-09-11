import PySimpleGUI as sg
from window import Window
import os
import json
import time

window = Window()
curr_window = window.get_curr_window()

PBE_SIMPLE_DICT = 'examples/pbe_simple/'
PBE_PROGRAM_DICT = 'examples/pbe_program/'
ASSERT_SIMPLE_DICT = 'examples/assert_simple/'
ASSERT_PROGRAM_DICT = 'examples/assert_program/'


working_wp = False




def run_pbe_simple_synth():
    global curr_window,text_ex,text_prog,working_wp
    text_ex.insert("end", "Example:\n", "example")
    text_prog.insert("end", "Program:\n", "program")
    examples_dict = read_jsons_from_dir(PBE_SIMPLE_DICT)
    for file_name, example in examples_dict.items():
       time.sleep(10)
       print("Example: ",example['P'])
       working_wp = False

def run(synthesizer_mode):
    global curr_window, working_wp,text_ex,text_prog
    text_ex = curr_window["-OUT_EXAMPLE-"].Widget
    text_ex.tag_config("example", foreground="orange")
    text_prog = curr_window["-OUT_PROG-"].Widget
    text_prog.tag_config("program", foreground="cyan")
    if not working_wp:
        working_wp = True
        if(synthesizer_mode == 'PBE - Simple'): curr_window.perform_long_operation(lambda: run_pbe_simple_synth(), '-OPERATION DONE-')
        elif(synthesizer_mode == 'PBE - As Part Of Program'): curr_window.perform_long_operation(lambda: run_pbe_program_synth(), '-OPERATION DONE-')
        elif(synthesizer_mode == 'ASSERT - Simple'): curr_window.perform_long_operation(lambda: run_assert_simple_synth(), '-OPERATION DONE-')
        elif(synthesizer_mode == 'ASSERT - As Part Of Program'): curr_window.perform_long_operation(lambda: run_assert_program_synth(), '-OPERATION DONE-')
    else: sg.popup_quick_message("Running right now\nPlease wait until finish running the program",auto_close_duration=3)

def run_assert_simple_synth():
    raise NotImplementedError

def run_pbe_program_synth():
    raise NotImplementedError

def run_assert_program_synth():
    raise NotImplementedError



def read_jsons_from_dir(directory_path):
    # Initialize an empty dictionary to store the data
    data_dict = {}

    # Loop through the files in the directory
    for root, dirs, files in os.walk(directory_path):
        for file in files:
            # Check if the file ends with ".json"
            if file.endswith(".json"):
                # Construct the full file path
                file_path = os.path.join(root, file)
                file_name = file.split('.')[0]
                
                # Open and read the JSON file
                with open(file_path, 'r') as json_file:
                    # Load the JSON data into a dictionary
                    json_data = json.load(json_file)
                    
                    # Extract the relevant information
                    program = json_data['program']
                    linv = json_data['linv']
                    pvars = json_data['pvars']
                    P = json_data['P']
                    Q = json_data['Q']
                    
                    # Store the data in the dictionary
                    data_dict[file_name] = {'program': program, 'linv': linv, 'pvars': pvars, 'P': P, 'Q': Q}
    
    return data_dict




def process_user_input():
    global window,curr_window,working_wp
   
    event, values = curr_window.read()
    while not (event == sg.WIN_CLOSED or event=="Exit"):
        if event == "Go":
            synthesizer_mode = values["-SYNTH_MODE-"]
            run(synthesizer_mode)
        elif event == "Next Example":
            if not working_wp:
                curr_window["-OUT_EXAMPLE-"].update("")
                curr_window["-OUT_PROG-"].update("")
                synthesizer_mode = values["-SYNTH_MODE-"]
            else: sg.popup_quick_message("Running right now\nPlease wait until finish running the program",auto_close_duration=3)
        elif event == "Run Through Examples":
            curr_window.close()
            curr_window = window.set_layout(window.get_examples_layout())
        elif event == "User Input":
            curr_window.close()
            curr_window = window.set_layout(window.get_examples_layout())
        elif event == "Main Menu":
            curr_window.close()
            curr_window = window.set_layout(window.get_main_layout())
                
        event, values = curr_window.read()
    curr_window.close()

if __name__ == '__main__':
    process_user_input()