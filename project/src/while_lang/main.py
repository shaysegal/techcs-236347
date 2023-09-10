import PySimpleGUI as sg
from window import Layout
import os
import json

window = Layout().getMainLayout()

def run_pbe_synth(file_path, synthesizer_mode):
    raise NotImplementedError

def run_assert_synth(file_path, synthesizer_mode):
    raise NotImplementedError



def process_user_input():
    global window
   
    event, values = window.read()
    while not (event == sg.WIN_CLOSED or event=="Exit"):
        if event == "Submit":
            file_path = values["-FILE-"]
            synthesizer_mode = values["-SYNTH_MODE-"]
            if(synthesizer_mode == 'PBE'): run_pbe_synth(file_path, synthesizer_mode)
            elif(synthesizer_mode == 'Assert'): run_assert_synth(file_path, synthesizer_mode)
        event, values = window.read()
    window.close()

if __name__ == '__main__':
    # process_user_input()
    # symbols = ['MSFT','NVDA']
    # for sym in symbols:
    #     pass

    # Define the directory path where your JSON files are located
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
                    
                    # Store the data in the data_dict using a hierarchical structure
                    data_dict.setdefault('examples', {}).setdefault('simple_pbe', {})[file] = {
                        'program': program,
                        'linv': linv,
                        'pvars': pvars,
                        'P': P,
                        'Q': Q
                    }

            