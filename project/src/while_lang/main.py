import PySimpleGUI as sg
from window import Window
import os
import json

window = Window()
curr_window = window.get_curr_window()

def run_pbe_synth(file_path, synthesizer_mode):
    raise NotImplementedError

def run_assert_synth(file_path, synthesizer_mode):
    raise NotImplementedError



def process_user_input():
    global window,curr_window
   
    event, values = curr_window.read()
    while not (event == sg.WIN_CLOSED or event=="Exit"):
        if event == "Go":
            file_path = values["-SYNTH_MODE-"]
            synthesizer_mode = values["-SYNTH_MODE-"]
            if(synthesizer_mode == 'PBE - Simple'): run_pbe_synth(file_path, synthesizer_mode)
            elif(synthesizer_mode == 'PBE - As Part Of Program'): run_assert_synth(file_path, synthesizer_mode)
            elif(synthesizer_mode == 'ASSERT - Simple'): run_assert_synth(file_path, synthesizer_mode)
            elif(synthesizer_mode == 'ASSERT - As Part Of Program'): run_assert_synth(file_path, synthesizer_mode)
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
    directory_path = 'examples/simple_pbe/'

    # Initialize an empty dictionary to store the data
    data_dict = {}

    # Loop through the files in the directory
    for root, dirs, files in os.walk(directory_path):
        for file in files:
            # Check if the file ends with ".json"
            if file.endswith(".json"):
                # Construct the full file path
                file_path = os.path.join(root, file)
                
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
                    