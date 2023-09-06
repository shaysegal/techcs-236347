from z3 import Int,String, ForAll, Implies, Not, And, Or, Solver, unsat, sat,Length,Concat,IndexOf
import z3


program =  "sum := ??"
linv = lambda d: d['y'] >= 0
pvars = ['a', 'b', 'sum']
#var_types={
#    'a':Int,
#    'b':Int,
#    'sum':Int
#}
var_types={
    'a':String,
    'b':String,
    'sum':String
}
examples =[]
example1 = {}
#example1['P'] = lambda d: d['a'] == 3 and d['b'] == 4 and d['sum'] == 0
#example1['Q'] = lambda d: d['a'] == 3 and d['b'] == 4 and d['sum'] == 12
example1['P'] = lambda d: d['a'] == 'abc' and d['b'] == 'aaa' and d['sum'] == ''
example1['Q'] = lambda d: d['a'] == 'abc' and d['b'] == 'aaa' and d['sum'] == 'abcaaa'
examples.append(example1)
example2 = {}
#example2['P'] = lambda d: d['a'] == 5 and d['b'] == 2 and d['sum'] == 0
#example2['Q'] = lambda d: d['a'] == 5 and d['b'] == 2 and d['sum'] == 10
example2['P'] = lambda d: d['a'] == 'abc' and d['b'] == 'bab' and d['sum'] == ''
example2['Q'] = lambda d: d['a'] == 'abc' and d['b'] == 'bab' and d['sum'] == 'abcbab'
examples.append(example2) 
# find god_program
first_example = True
god_program = None
Q_values_store=[]




program =  "t := x * ??"
linv = lambda d: d['x'] >= 0
pvars = ['t', 'x']
var_types={
    't':Int,
    'x':Int
}
examples =[]
example1 = {}
example1['P'] = lambda d: d['t'] == 0 and d['x'] == 2
example1['Q'] = lambda d: d['t'] == 6 and d['x'] == 2
examples.append(example1)
example2 = {}
example2['P'] = lambda d: d['t'] == 0 and d['x'] == 3
example2['Q'] = lambda d: d['t'] == 9 and d['x'] == 3