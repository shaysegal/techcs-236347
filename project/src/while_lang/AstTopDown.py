import ast
from copy import deepcopy

import shortuuid




pick_new_identifer = lambda : 'v_'+shortuuid.ShortUUID().random(length=4)

#ast.Lambda,ast.Set,ast.Tuple
expr_allowed_classes = [ast.BoolOp , ast.NamedExpr ,ast.BinOp ,ast.UnaryOp  ,ast.IfExp , ast.Dict  , ast.Compare ,ast.Call  ,ast.Attribute , ast.Subscript,ast.Name ,ast.List ,ast.Slice] 
#expr_context = ast.Load | ast.Store | ast.Del
#boolop = ast.And | ast.Or
operator = [ast.Add , ast.Sub , ast.Mult, ast.Div, ast.Mod , ast.Pow , ast.LShift , ast.RShift , ast.BitOr, ast.BitXor , ast.BitAnd , ast.FloorDiv]
unaryop = [ast.Invert , ast.Not , ast.UAdd , ast.USub]
cmpop = [ast.Eq , ast.NotEq , ast.Lt , ast.LtE , ast.Gt , ast.GtE , ast.Is , ast.IsNot , ast.In , ast.NotIn]

__options = [ast.Expression()]

def TopDownGen():
    for op in __options:
        yield op
        

def is_concrete(ast_tree):
    return all(isinstance(e, (ast.cmpop , ast.operator , ast.unaryop , ast.boolop , ast.Name , ast.Constant)) 
    for e in filter(lambda n : is_leaf(n),ast.walk(ast_tree)))
    

def to_prune(ast):
    return False

#has no AST children
def is_leaf(ast_node):
    # ast.iter_fields(ast_node) return (name,value) tuple
    #ret = list(filter(lambda tupl: any(isinstance(e, ast.AST) for e in tupl[1]) if isinstance(tupl[1],list) else isinstance(tupl[1],ast.AST) ,ast.iter_fields(ast_node)))
    return len(list(ast.iter_child_nodes(ast_node)))==0


class TransformLeaves(ast.NodeTransformer):
    def __init__(self, referance ,new_node):
        self.ref = referance
        self.new_n = new_node
    def generic_visit(self, node):
        super().generic_visit(node)
        if node == self.ref:
            return self.new_n
        return node
def extend_middle_node_with_stars(node):
    match type(node):
        case ast.BoolOp:
            node.values.append(ast.expr())
        case ast.Dict:
            node.keys.append(ast.expr())
            node.values.append(ast.expr())
            
        case ast.Compare:
            node.ops.append(ast.cmpop())
            node.comparators.append(ast.expr())
        case ast.List:
            node.elts.append(ast.expr())

    return

def has_immidiate_stars_childern(node):
    #this types has * in one of their children , which mean we need to enable any number of children in there
    return type(node) in [ast.BoolOp,ast.Dict,ast.Compare,ast.List]

def extend_leaf(leaf):
    extend_leafs = []
    match type(leaf):
        case ast.Expression:
            l=deepcopy(leaf)
            l.body= ast.expr()
            extend_leafs += [l]
        case ast.expr:
            extend_leafs += list(map (lambda o: o(),expr_allowed_classes))
            extend_leafs.append(ast.Constant(value=None))
        case ast.cmpop:
            extend_leafs += list(map (lambda o: o(),cmpop))
        case ast.BoolOp:
            #TODO update to consider *expr
            l1=deepcopy(leaf)
            l2=deepcopy(leaf)
            l1.op = ast.Or()
            l2.op = ast.And()
            l1.values = [ast.expr(),ast.expr()]
            l2.values = [ast.expr(),ast.expr()]
            extend_leafs += [l1,l2]
        case ast.NamedExpr:
            l = deepcopy(leaf)
            l.target = ast.expr()
            l.value = ast.expr()
            extend_leafs += [l]
        case ast.BinOp:
            for op in operator:
                temp = deepcopy(leaf)
                temp.op = op()
                temp.left = ast.expr()
                temp.right = ast.expr()
                extend_leafs.append(temp)
        case ast.UnaryOp:
            for op in unaryop:
                temp = deepcopy(leaf)
                temp.op = op()
                temp.operand = ast.expr()
                extend_leafs.append(temp)
        #put lambda on the side for now, will return later
        #case ast.Lambda:
            #TODO update to consider *args
        case ast.IfExp:
            l1 = deepcopy(leaf)
            l1.test = ast.expr()
            l1.body = ast.expr()
            l2 = deepcopy(leaf)
            l2.test = ast.expr()
            l2.body = ast.expr()
            l2.orelse = ast.expr()
            extend_leafs += [l1,l2]
        case ast.Dict:
            l = deepcopy(leaf)
            l.keys = []
            l.values = []
            extend_leafs.append(l)
        case ast.Compare:
            for op in cmpop:
                temp = deepcopy(leaf)
                temp.left = ast.expr()
                temp.comperators = [ast.expr()]
                temp.ops = [op()]
                extend_leafs.append(temp)

#        case ast.Call :
#            l = deepcopy(leaf)
#            l.func 
#            l.args          
#           extend_leafs.append(temp)

        case ast.Constant :
            l = deepcopy(leaf)
            l.value = pick_new_identifer()
            extend_leafs.append(l)
        case ast.List:
            l = deepcopy(leaf)
            l.elts = []
            extend_leafs.append(l)
        case ast.Slice:
            l = deepcopy(leaf)
            l.lower = ast.expr()
            l.upper = ast.expr()
            l.step = ast.expr()
            extend_leafs.append(l)
        case ast.Attribute :
            l = deepcopy(leaf)
            l.value = ast.expr()
            l.attr = pick_new_identifer()
            extend_leafs.append(l)
        #TODO case ast.Subscript:
        case ast.Name:
            l = deepcopy(leaf)
            l.id = pick_new_identifer()
            extend_leafs.append(l)

    return extend_leafs

def extend():
    new_options = []
    for op in globals()['__options']:
        if is_leaf(op):
            new_options += extend_leaf(op)
        else: # not leaf .. 
            to_search = list(ast.iter_child_nodes(op))
            for c in to_search:
                c.parent = op 
            while(len(to_search)>0):
                child = to_search.pop(0)                
                if is_leaf(child):
                    if is_concrete(child):
                        continue
                    #TODO: need to figure out how to find the "dad" and create deep copies of all the options 
                    new_leafs = extend_leaf(child)
                    init_ref = child
                    for n_leaf in new_leafs :
                        TransformLeaves(init_ref,n_leaf).visit(child.parent)
                        #we need the whole tree as the "option"
                        new_options+=[deepcopy(op)]
                        init_ref = n_leaf
                else:
                    #take care of trees with collections (lists,args,etc) 
                    if is_concrete(child) and has_immidiate_stars_childern(child):
                        
                        new_options+= extend_middle_node_with_stars(child)
                        continue
                    # append all children to continue the search 
                    childern = list (ast.iter_child_nodes(child))
                    for c in childern:
                        c.parent = child 
                    to_search += childern

    globals()['__options'] = new_options
    return 



while(True):
    it = TopDownGen()
    while(True):
        try:
            cand = next(it)
            if to_prune(cand):
                print("not relevant option")
            elif not is_concrete(cand):
                print("might be relevant option, but still not concerte, cand: ",ast.dump(cand))
            else: #concerete and not pruned
                print("try this aginst input, cand:" , ast.dump(cand))
        except StopIteration:
            print("need to extend the options")
            extend()
            break

