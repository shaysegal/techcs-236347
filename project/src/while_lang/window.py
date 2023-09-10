import PySimpleGUI as sg

class Layout:
    def __init__(self):
        sg.theme("DarkPurple4") 
        # sg.theme("DarkBlue7") 
        # sg.theme("DarkAmber")

        self.layout_input = [[sg.T("")],
        [sg.Text("Please Enter Synth Mode: ",font=("Comic Sans MS",18)), sg.Combo(key="-SYNTH_MODE-" ,values=["Simple PBE","Strings PBE",'Assert'], default_value="Simple PBE",font=("Comic Sans MS",16))],
        [sg.T("")],
        [sg.Button("Go",font=("Comic Sans MS",18),size=(6,1))]]

        self.layout_examples = [[sg.Text("Example:", font=("Comic Sans MS", 16))],
        [sg.Multiline(key='-OUT_EXAMPLE-', size=(60, 15),reroute_stdout=True,autoscroll=True,font=("Comic Sans MS",12),text_color="yellow")]]

        self.layout_programs = [[sg.Text("Programs:", font=("Comic Sans MS", 16))],
        [sg.Multiline(key='-OUT_EXAMPLE-', size=(75, 15),reroute_stdout=True,autoscroll=True,font=("Comic Sans MS",12),text_color="yellow")]]

        self.exit_layout = [sg.Button("Exit",size=(8,1),button_color=('red','#fdcb52'),font=("Comic Sans MS",13))]
        
        layout = [[sg.Column(self.layout_input, element_justification='c')],
                    [sg.T("")],
                    [sg.Column(self.layout_examples, element_justification='l'),sg.VSeperator(),sg.Column(self.layout_programs, element_justification='l')],
                    [sg.T("")],
                    [sg.T("")],
                    [sg.T("")],
                    [sg.T("")],
                    [sg.Text(text=(""),size=(160,1)),sg.Button("Exit",size=(8,1),button_color=('red','#fdcb52'),font=("Comic Sans MS",13))]]
        self.main_window = sg.Window('Synthesizer',layout, size=(1500,800),element_justification='center')

    def getMainLayout(self):
        return self.main_window
