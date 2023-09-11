import PySimpleGUI as sg

class Window:
    def __init__(self):
        sg.theme("DarkPurple4") 
        # sg.theme("DarkBlue7") 
        # sg.theme("DarkAmber")

        self.curr_window = sg.Window('Synthesizer',self.get_main_layout(), size=(1500,800),element_justification='center')


    def get_curr_window(self):
        return self.curr_window
    
    def set_layout(self,layout):
        self.curr_window = sg.Window('Synthesizer',layout, size=(1500,800),element_justification='center')
        return self.curr_window
    def get_examples_layout(self):

        col_mode = [[sg.T("")],
        [sg.Text("Please Enter Synth Mode: ",font=("Comic Sans MS",18)), sg.Combo(key="-SYNTH_MODE-" ,values=["PBE - Simple","PBE - As Part Of Program","ASSERT - Simple","ASSERT - As Part Of Program"], default_value="Simple PBE",font=("Comic Sans MS",16))],
        [sg.T("")],
        [sg.Button("Go",font=("Comic Sans MS",18),size=(6,1))]]

        col_examples = [[sg.Text("Example:", font=("Comic Sans MS", 16))],
        [sg.Multiline(key='-OUT_EXAMPLE-', size=(60, 15),reroute_stdout=True,autoscroll=True,font=("Comic Sans MS",12),text_color="yellow")]]

        col_programs = [[sg.Text("Programs:", font=("Comic Sans MS", 16))],
        [sg.Multiline(key='-OUT_EXAMPLE-', size=(75, 15),reroute_stdout=True,autoscroll=True,font=("Comic Sans MS",12),text_color="yellow")]]
        
        examples_layout = [[sg.Column(col_mode, element_justification='c')],
                    [sg.T("")],
                    [sg.Column(col_examples, element_justification='l'),sg.VSeperator(),sg.Column(col_programs, element_justification='l')],
                    [sg.T("")],
                    [sg.T("")],
                    [sg.T("")],
                    [sg.T("")],
                    [sg.Button("Main Menu",size=(12,1),button_color=('purple','#fdcb52'),font=("Comic Sans MS",13)),sg.Text(text=(""),size=(3,1)),sg.Button("Exit",size=(10,1),button_color=('red','#fdcb52'),font=("Comic Sans MS",13))]]
        return examples_layout
    

    def get_main_layout(self):
        main_layout = [[sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.Text("Welcome to our Synthesizer :)",font=("Comic Sans MS",18))],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.Button("Run Through Examples",size=(20,2),button_color=('white','#BF40BF'),font=("Comic Sans MS",13)),sg.Button("User Input",size=(15,2),button_color=('white','#BF40BF'),font=("Comic Sans MS",13))],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.Text(text=(""),size=(160,1)),sg.Button("Exit",size=(10,1),button_color=('red','#fdcb52'),font=("Comic Sans MS",14))]]
        
        return main_layout