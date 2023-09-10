import PySimpleGUI as sg
from window import Layout

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
    process_user_input()
    # symbols = ['MSFT','NVDA']
    # for sym in symbols:
    #     pass
        