# Program Synthesizer

## Synthesizer Modes:
Our synthesizer operates in four primary modes:
- Run through examples: which allows the user to learn and test the synthesizer abilities, by going over a set of preconstructed, diverse and comprehensive examples.
- User input: allows the user to utillize the full potential of the synthesizer, and write his own program with matching constraints , and recieve the synthesized code.



## Synthesizer Ability:
- PBE Mode: In this mode, our synthesizer generates Python programs based on provided input-output examples.

- ASSERT Mode: In this mode, our synthesizer can handle simple assertions in programs.
  
- Our code synthesizer can get as User Input in both modes and Synthesize a program based on the input. Our synthesizer sketch support Integers and Strings.
  
*simple Mode: runs through examples of PBE and ASSERT that are simple assign.

## Synthesizer Limits:
- 
-
-
- 

## Usage

#### Run Through Examples mode:
1. Click on the "Run Through Examples" button in the main menu.
2. choose the constraints type on the upper checkbox (PBE or ASSERT).
3. Click the "GO" button to start viewing the examples.
4. Click "Next Example" to continue to the next example program

#### User Input mode:
1. Click on the "Usert Input" button in the main menu.
2. choose the constraints type on the upper checkbox (PBE or ASSERT).
3. Insert the needed constraints in the same format seen in the examples.
4. Insert wanted program to complete, with the sketch hold in a place suitable for the given Synth abilities metioned above.
5. Click the "Synth Program" button to get the fully completed code. Click on "Resert" or "Reset ALL" to change tour input.

** The convention of inputs:
- PVars should be of format: ['S'] where S is a string
- 
-
-

## Setup
(on a unix based system or WSL enviroment)

python version must be AT LEAST 3.10.*

1. pull the git reposetory of the project using:
```console
git pull https://github.com/shaysegal/techcs-236347/tree/master
```

2. install z3 solver on the enviroment:
```console
pip install z3-solver
```

3. install tkinter on the enviroment:
```console
pip install tk
```
for mac users you might also need to do
```console
brew install python-tk
```

4. install pysimplegui on the enviroment:
```console
pip install pysimplegui
```

#### To run the synthisizer, run the main.py file in the repo.

## Demo

A demo of the User Input mode:

1. Click on the "Usert Input" button in the main menu.
![Example Image 1](./pics/1.png)

2. choose the constraints type on the upper checkbox (PBE or ASSERT).
![Example Image 2](./pics/2.png)

3. Insert the needed constraints in the same format seen in the examples.
4. Insert wanted program to complete, with the sketch hold in a place suitable for the given Synth abilities metioned above.
5. Click the "Synth Program" button to get the fully completed code on the right "Programs" window. Click on "Resert" or "Reset ALL" to change tour input.
![Example Image 3](./pics/3_4.png)
