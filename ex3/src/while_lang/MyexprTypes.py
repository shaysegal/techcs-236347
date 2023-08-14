
from enum import IntEnum

def default_good_size_tuple(sizes):
    return True
def partitions(n, k):
    """generate all splits of n into k components. Order
    "of the split components is considered relevant.
    """
    if (n < k):
        raise ValueError('n must be greater than or equal to k in call ' +
                            'to utils.partitions(n, k)')

    cuts = []
    cuts.append(0)
    cuts.append(n-k+1)
    for i in range(k - 1):
      cuts.append(n - k + 1 + i + 1)

    done = False

    while (not done):
        retval = tuple([cuts[i] - cuts[i-1] for i in range(1, k+1)])
        rightmost = 0
        for i in range(1,k):
            if cuts[i] - cuts[i - 1] > 1:
                rightmost = i
                cuts[i] = cuts[i] - 1
                break
        if rightmost == 0:
            done = True
        else:
            accum = 1
            for i in reversed(range(1, rightmost)):
                cuts[i] = cuts[rightmost] - accum
                accum = accum + 1
        yield retval
def cartesian_product_of_generators(*generators):
    """A generator that produces the cartesian product of the input
    "sub-generators."""
    tuple_size = len(generators)
    if (tuple_size == 1):
        for elem in generators[0].generate():
            yield (elem, )

    else:
        for sub_tuple in cartesian_product_of_generators(*generators[1:]):
            for elem in generators[0].generate():
                yield (elem, ) + sub_tuple


class TypeCodes(IntEnum):
    """An (extensible) set of type codes. There must be
    (at least) one class deriving from TypeBase for each of these
    type codes."""

    boolean_type = 1
    integer_type = 2
    bit_vector_type = 3
    string_type = 4

class TypeBase(object):
    """Base class for all types. Only handles type codes."""

    def __init__(self, type_code):
        global _type_id_counter
        self.type_code = type_code
        self.type_id = _type_id_counter
        _type_id_counter += 1

    def __str__(self):

        raise NotImplementedError

    def __repr__(self):
        raise NotImplementedError

    def get_smt_type(self, smt_context_object):
        raise NotImplementedError

class _BoolType(TypeBase):
    """A Boolean Type."""

    def __init__(self):
        super().__init__(TypeCodes.boolean_type)

    def __str__(self):
        return 'BooleanType'

    def __repr__(self):
        return 'BooleanType'

    def __hash__(self):
        return hash(TypeCodes.boolean_type)

    def get_smt_type(self, smt_context_object):
        return smt_context_object.make_bool_sort()

    def print_string(self):
        return 'Bool'

_boolean_type_instance = _BoolType()

def BoolType():
    return _boolean_type_instance


class GeneratorBase(object):
    object_counter = 0

    def __init__(self, name = None):
        if (name != None or name != ''):
            self.name = name
        else:
            self.name = 'AnonymousGenerator_%d' % self.object_counter
        self.object_counter += 1

    def generate(self):
        raise NotImplementedError

    def set_size(self, new_size):
        raise NotImplementedError

    def clone(self):
        raise NotImplementedError



class LeafGenerator(GeneratorBase):
    """A generator for leaf objects.
    Variables, constants and the likes."""

    def __init__(self, leaf_objects, name = None):
        super().__init__(name)
        self.leaf_objects = list(leaf_objects)
        self.iterable_size = len(self.leaf_objects)
        self.allowed_size = 0

    def generate(self):
        current_position = 0
        if (self.allowed_size != 1):
            return

        while (current_position < self.iterable_size):
            retval = self.leaf_objects[current_position]
            current_position += 1
            yield retval

    def set_size(self, new_size):
        self.allowed_size = new_size

    def clone(self):
        return LeafGenerator(self.leaf_objects, self.name)


class NonLeafGenerator(GeneratorBase):
    """A generator with sub generators."""

    def __init__(self, sub_generators, name=None):
        super().__init__(name)
        self.sub_generators = [x.clone() for x in sub_generators]
        self.arity = len(sub_generators)
        self.allowed_size = 0
        assert self.arity > 0
        self.good_size_tuple = default_good_size_tuple

    def set_size(self, new_size):
        self.allowed_size = new_size

    def _set_sub_generator_sizes(self, partition):
        assert (len(partition) == self.arity)

        for i in range(self.arity):
            self.sub_generators[i].set_size(partition[i])
        return

    def _instantiate(self, sub_exprs):
        raise NotImplementedError('NonLeafGenerator._instantiate()')

    def generate(self):
        if (self.allowed_size - 1 < self.arity):
            return

        for partition in partitions(self.allowed_size - 1, self.arity):
            if not self.good_size_tuple(partition):
                continue
            self._set_sub_generator_sizes(partition)
            for product_tuple in cartesian_product_of_generators(*self.sub_generators):
                yield self._instantiate(product_tuple)


class ExpressionTemplateGenerator(NonLeafGenerator):
    """A generator for expressions with placeholders."""

    def __init__(self, expr_template, place_holder_vars, sub_generators, good_size_tuple, name=None):
        super().__init__(sub_generators, name)
        self.expr_template = expr_template
        self.place_holder_vars = place_holder_vars
        assert len(place_holder_vars) == len(sub_generators)
        if good_size_tuple is not None:
            self.good_size_tuple = good_size_tuple

    def _instantiate(self, sub_exprs):
        # print('TEMPLATE:', exprs.expression_to_string(self.expr_template))
        # print('PHS:', [ exprs.expression_to_string(p) for p in self.place_holder_vars ])
        # print('SUBS:', [ exprs.expression_to_string(s) for s in sub_exprs ])
        ret = substitute_all(self.expr_template, list(zip(self.place_holder_vars, sub_exprs)))
        # print('RES:', exprs.expression_to_string(ret))
        return ret

    def clone(self):
        return ExpressionTemplateGenerator(
                self.expr_template,
                self.place_holder_vars,
                [x.clone() for x in self.sub_generators],
                self.good_size_tuple,
                self.name)