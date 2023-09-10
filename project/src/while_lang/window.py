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
    
#     colR1C1 = [[sg.Text('2'*40)],
#             [sg.Button('button', key='ButtonOne')],
#            [sg.CB('Check 1')]]

# colR1C2 = [[sg.Text('1'*40)],
#             [sg.Text('some text...', key='TextOne')],
#            [sg.CB('Check 2')]]

# layout = [[sg.Column(colR1C1, background_color='red', element_justification='left'),
#            sg.Column(colR1C2, background_color='blue', element_justification='right')]]

# window = sg.Window('Window Title', layout)
# event, values = window.Read()
    

    #  account_details_column = [
    #     [sg.Button("Run Full Automate Strategy",font=('16'),button_color=('black','goldenrod2')), sg.T("   "), sg.Button("Run Semi Automate Strategy",font=('16'),button_color=('black','goldenrod2'))],
    #     [sg.T("")],
    #     [sg.Button("Update Account",font=('12')),sg.Button("Show Portfolio",font=('12')),sg.Button("Show Orders",font=('12'))],
    #     [sg.Text("Sectors Sentiment: ",font=('14')),sg.Text(text_color='white',font=('14'),key='-SECTORS_SENTIMENT-'),sg.Text("Markets Sentiment: ",font=('14')),sg.Text(text_color='white',font=('14'),key='-MARKETS_SENTIMENT-')],
    #     [sg.Text("Account ID: ",font=('14')),sg.Text(text_color='white',font=('14'),key='-ACCOUNT_ID-')],
    #     [sg.Text("Cash Balance: ",font=('14')),sg.Text(text_color='white',font=('14'),key='-ACCOUNT_CASH-')],
    #     [sg.Text("Equity: ",font=('14')),sg.Text(text_color='white',font=('14'),key='-ACCOUNT_EQUITY-')],
    #     ]

    #     orders_column = [
    #     [sg.Text("Today Return: ",font=('14')),sg.Text(text_color='white',font=('14'),key='-TODAY_RETURN-')],
    #     [sg.Text("Realized Return(%): ",font=('14')),sg.Text(text_color='white',font=('14'),key='-REALIZED_RETURN-')],
    #     [sg.Text("Unrealized Return(%): ",font=('14')),sg.Text(text_color='white',font=('14'),key='-UNREALIZED_RETURN-')]]

    #     self.tradestation_layout = [
    #     [sg.Column(account_details_column,justification='left'),sg.VSeparator(pad=(100,0)),sg.Column(orders_column)],
    #     [sg.T("")],
    #     [sg.Output(key='-OUT1-', size=(150, 20))],
    #     [sg.Button("Exit",size=(8,1),font=('12'))]]             

    # def getMainLayout(self):
    #     return self.layout_main
    
    # def get_tradestation_layout(self):
    #     return self.tradestation_layout
    
    # def setWindow(self, layout,position='c'):
    #     return sg.Window('NewsToGod',layout, size=(1250,750),element_justification=position)
    