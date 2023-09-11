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
        [sg.Text("Please Enter Synth Mode: ",font=("Comic Sans MS",18)), sg.Combo(key="-SYNTH_MODE-" ,values=["PBE - Simple","PBE - As Part Of Program","ASSERT - Simple","ASSERT - As Part Of Program"], default_value="PBE - Simple",font=("Comic Sans MS",16))],
        [sg.T("")],
        [sg.Button("Go",font=("Comic Sans MS",18),size=(6,1))]]

        col_examples = [[sg.Text("Examples:", font=("Comic Sans MS", 16))],
        [sg.Multiline(key='-OUT_EXAMPLE-', size=(65, 15),reroute_stdout=False,autoscroll=True,font=("Comic Sans MS",12),text_color="yellow")]]

        col_programs = [[sg.Text("Programs:", font=("Comic Sans MS", 16))],
        [sg.Multiline(key='-OUT_PROG-', size=(70, 15),reroute_stdout=False,autoscroll=True,font=("Comic Sans MS",12),text_color="yellow")]]
        
        examples_layout = [[sg.Column(col_mode, element_justification='c')],
                    [sg.T("")],
                    [sg.Column(col_examples, element_justification='l'),sg.VSeperator(),sg.Column(col_programs, element_justification='l')],
                    [sg.T("")],
                    [sg.Button("Next Example",size=(12,1),font=("Comic Sans MS",13))],
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
                            [sg.Button("Documentation",size=(30,2),button_color=('white','#BF40BF'),font=("Comic Sans MS",16))],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.Button("Run Through Examples",size=(20,2),button_color=('white','#BF40BF'),font=("Comic Sans MS",15)),sg.Button("User Input",size=(15,2),button_color=('white','#BF40BF'),font=("Comic Sans MS",15))],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.T("")],
                            [sg.Text(text=(""),size=(160,1)),sg.Button("Exit",size=(10,1),button_color=('red','#fdcb52'),font=("Comic Sans MS",14))]]
        
        return main_layout
    def get_user_layout(self):
        col_mode = [[sg.T("")],
        [sg.Text("Please Enter Synth Mode: ",font=("Comic Sans MS",18)), sg.Combo(key="-SYNTH_MODE-" ,values=["PBE - Simple","PBE - As Part Of Program","ASSERT - Simple","ASSERT - As Part Of Program"], default_value="PBE - Simple",font=("Comic Sans MS",16))],
        [sg.T("")],
        [sg.Button("Synth Program",font=("Comic Sans MS",16),size=(12,1))]]
        col_inputs = [[sg.Text("Pvars: ",font=("Comic Sans MS",14)), sg.Input(key="-PVARS-" ,change_submits=True,font=("Comic Sans MS",12),size=(70,1))],
                    [sg.Text("Linv:   ",font=("Comic Sans MS",14)), sg.Input(key="-LINV-" ,change_submits=True,font=("Comic Sans MS",12),size=(70,1))],
                    [sg.Text("P:       ",font=("Comic Sans MS",14)), sg.Input(key="-P-" ,change_submits=True,font=("Comic Sans MS",12),size=(70,1))],
                    [sg.Text("Q:      ",font=("Comic Sans MS",14)), sg.Input(key="-Q-" ,change_submits=True,font=("Comic Sans MS",12),size=(70,1))],
                    [sg.Text("Program: ",font=("Comic Sans MS",14)), sg.Multiline(key="-INPUT_PROG-" ,size=(66,10),reroute_stdout=False,autoscroll=True,font=("Comic Sans MS",12),text_color="yellow")]]

        col_programs = [[sg.Text("Programs:", font=("Comic Sans MS", 16))],
        [sg.Multiline(key='-OUT_PROG-', size=(70, 15),reroute_stdout=False,autoscroll=True,font=("Comic Sans MS",12),text_color="yellow")]]
        
        user_layout = [[sg.Column(col_mode, element_justification='c')],
                    [sg.T("")],
                    [sg.Column(col_inputs, element_justification='l'),sg.VSeperator(),sg.Column(col_programs, element_justification='l')],
                    [sg.T("")],
                    [sg.Button("Reset ALL",size=(12,1),font=("Comic Sans MS",13)),sg.Button("Reset",size=(12,1),font=("Comic Sans MS",13))],
                    [sg.T("")],
                    [sg.T("")],
                    [sg.T("")],
                    [sg.Button("Main Menu",size=(12,1),button_color=('purple','#fdcb52'),font=("Comic Sans MS",13)),sg.Text(text=(""),size=(3,1)),sg.Button("Exit",size=(10,1),button_color=('red','#fdcb52'),font=("Comic Sans MS",13))]]
        return user_layout
    
    def get_documentation_layout(self):
        documentation_layout = [
            [sg.T("")],
            [sg.T("Documentation", font=("Comic Sans MS", 20))],
            [sg.T("")],
            [sg.Text(
                key='-DOCS-',
                size=(90, 20),
                text="Welcome to the Synthesizer Documentation!\n\n"
                    "This synthesizer tool is designed to help you generate and run programs using various synthesis modes.\n"
                    "Here are some examples of how to use the synthesizer:\n\n"
                    "1. Run Through Examples:\n"
                    "   Click the 'Run Through Examples' button to go through a list of predefined examples. Choose a synthesis mode\n"
                    "   and click 'Go' to run the selected example.\n\n"
                    "2. User Input:\n"
                    "   Click the 'User Input' button to input your own program, Pvars, Linv, P, Q, and synthesis mode.\n"
                    "   Then, click 'Synth Program' to run your custom program.\n\n"
                    "3. Documentation:\n"
                    "   Click the 'Documentation' button to view this documentation.\n\n"
                    "You can also reset input fields with the 'Reset' or 'Reset ALL' buttons.\n\n"
                    "Have fun experimenting with program synthesis!",
                font=("Comic Sans MS", 12),
                text_color="yellow"
            )],
            [sg.T("")],
            [sg.Button("Main Menu", size=(12, 1), button_color=('purple', '#fdcb52'), font=("Comic Sans MS", 13)),
            sg.Text(text=(""), size=(3, 1)),
            sg.Button("Exit", size=(10, 1), button_color=('red', '#fdcb52'), font=("Comic Sans MS", 13))]
        ]

        return documentation_layout
    

        
    def get_documentation_text(self):
        documentation_text = """
        Welcome to the Synthesizer Documentation!

        This synthesizer tool is designed to help you generate and run programs using various synthesis modes.
        Here are some examples of how to use the synthesizer:

        1. **Run Through Examples**:
        Click the "Run Through Examples" button to go through a list of predefined examples. Choose a synthesis mode
        and click "Go" to run the selected example.

        2. **User Input**:
        Click the "User Input" button to input your own program, Pvars, Linv, P, Q, and synthesis mode.
        Then, click "Synth Program" to run your custom program.

        3. **Documentation**:
        Click the "Documentation" button to view this documentation.

        You can also reset input fields with the "Reset" or "Reset ALL" buttons.

        Have fun experimenting with program synthesis!
        """
        return documentation_text