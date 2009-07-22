from __future__ import generators
from dispatch import *
from dispatch.strategy import Inequality, Signature, ExprBase, default
from dispatch.strategy import SubclassCriterion, NullCriterion
from dispatch.strategy import AbstractCriterion, Pointer, Predicate
from dispatch.ast_builder import build

import protocols, operator, dispatch
from types import NoneType

__all__ = [
    'Call',
    'AndCriterion', 'NotCriterion', 'TruthCriterion',
    'ExprBuilder', 'Const', 'Getattr', 'Tuple', 'dispatch_by_truth',
    'OrExpr', 'AndExpr', 'CriteriaBuilder', 'expressionSignature', 'IfElse',
]

# Helper functions for operations not supplied by the 'operator' module

def is_(o1,o2):
    return o1 is o2

def in_(o1,o2):
    return o1 in o2

def is_not(o1,o2):
    return o1 is not o2

def not_in(o1,o2):
    return o1 not in o2

def add_dict(d1,d2):
    d1 = d1.copy()
    d1.update(d2)
    return d1

try: frozenset
except NameError: from sets import ImmutableSet as frozenset
# XXX var, let, ???


class ExprBuilder:

    simplify_comparisons = True

    def __init__(self,arguments,*namespaces):
        self.arguments = arguments
        self.namespaces = namespaces

    def Name(self,name):
        if name in self.arguments:
            return self.arguments[name]

        for ns in self.namespaces:
            if name in ns:
                return Const(ns[name])

        raise NameError(name)

    def Const(self,value):
        return Const(value)

    _cmp_ops = {
        '>': operator.gt, '>=': operator.ge,
        '<': operator.lt, '<=': operator.le,
        '<>': operator.ne, '!=': operator.ne, '==':operator.eq,
        'in': in_, 'not in': not_in,
        'is': is_, 'is not': is_not
    }

    def Compare(self,initExpr,((op,other),)):
        return Call(
            self._cmp_ops[op], build(self,initExpr), build(self,other)
        )

    def IfElse(self, tval, cond, fval):
        return IfElse(build(self,tval), build(self,cond), build(self,fval))





    def mkBinOp(op):
        def method(self,left,right):
            return Call(op, build(self,left), build(self,right))
        return method

    LeftShift  = mkBinOp(operator.lshift)
    Power      = mkBinOp(pow)
    RightShift = mkBinOp(operator.rshift)
    Add        = mkBinOp(operator.add)
    Sub        = mkBinOp(operator.sub)
    Mul        = mkBinOp(operator.mul)
    Div        = mkBinOp(operator.div)
    Mod        = mkBinOp(operator.mod)
    FloorDiv   = mkBinOp(operator.floordiv)

    def multiOp(op):
        def method(self,items):
            result = build(self,items[0])
            for item in items[1:]:
                result = Call(op, result, build(self,item))
            return result
        return method

    Bitor      = multiOp(operator.or_)
    Bitxor     = multiOp(operator.xor)
    Bitand     = multiOp(operator.and_)

    def unaryOp(op):
        def method(self,expr):
            return Call(op, build(self,expr))
        return method

    UnaryPlus  = unaryOp(operator.pos)
    UnaryMinus = unaryOp(operator.neg)
    Invert     = unaryOp(operator.invert)
    Backquote  = unaryOp(repr)
    Not        = unaryOp(operator.not_)




    def tupleOp(op):
        def method(self,items):
            return Tuple(op,*[build(self,item) for item in items])
        return method

    Tuple = tupleOp(tuple)
    List  = tupleOp(list)

    def Dict(self, items):
        keys = Tuple(tuple, *[build(self,k) for k,v in items])
        vals = Tuple(tuple, *[build(self,v) for k,v in items])
        return Call(dict, Call(zip, keys, vals))

    def Subscript(self,left,right):
        left, right = build(self,left), build(self,right)
        if isinstance(right,tuple):
            return Call(operator.getslice,left,*right)
        else:
            return Call(operator.getitem,left,right)

    def Slice(self,start,stop):
        return build(self,start), build(self,stop)

    def Sliceobj(self,*args):
        return Call(slice,*[build(self,arg) for arg in args])

    def Getattr(self,expr,attr):
        expr = build(self,expr)
        if isinstance(expr,Const):
            return Const(getattr(expr.value,attr))
        return Getattr(expr,attr)

    def And(self,items):
        return AndExpr(*[build(self,expr) for expr in items])

    def Or(self,items):
        return OrExpr(*[build(self,expr) for expr in items])




    def CallFunc(self,funcExpr,args,kw,star,dstar):

        func = build(self,funcExpr)

        if isinstance(func,Const) and not kw and not star and not dstar:
            return Call(func.value, *[build(self,arg) for arg in args])

        elif kw or dstar or args or star:

            if args:
                args = Tuple(tuple,*[build(self,arg) for arg in args])
                if star:
                    args = Call(
                        operator.add, args, Call(tuple,build(self,star))
                    )

            elif star:
                args = build(self,star)

            if kw or dstar:

                args = args or Const(())

                if kw:
                    kw = self.Dict(kw)
                    if dstar:
                        kw = Call(add_dict, kw, build(self,dstar))
                elif dstar:
                    kw = build(self,dstar)

                return Call(apply, func, args, kw)

            else:
                return Call(apply, func, args)

        else:
            return Call(apply,func)




class LogicalExpr(ExprBase):

    def __new__(klass,*argexprs):
        for arg in argexprs:
            if not isinstance(arg,Const):
                return ExprBase.__new__(klass,*argexprs)
        return Const(klass.immediate([arg.value for arg in argexprs]))

    def __init__(self,*argexprs):
        self.argexprs = argexprs
        self.hash = hash((type(self),argexprs))

    def __eq__(self,other):
        return type(self) is type(other) and other.argexprs == self.argexprs


class OrExpr(LogicalExpr):

    """Lazily compute logical 'or' of exprs"""

    def asFuncAndIds(self,generic):

        argIds = map(generic.getExpressionId,self.argexprs)

        def or_(get):
            for arg in argIds:
                val = get(arg)
                if val:
                    break
            return val

        return or_, (EXPR_GETTER_ID,)

    [dispatch_as(classmethod)]
    def immediate(klass,seq):
        for item in seq:
            if item:
                break
        return item


class AndExpr(LogicalExpr):
    """Lazily compute logical 'and' of exprs"""

    def asFuncAndIds(self,generic):

        argIds = map(generic.getExpressionId,self.argexprs)

        def and_(get):
            for arg in argIds:
                val = get(arg)
                if not val:
                    break
            return val

        return and_, (EXPR_GETTER_ID,)

    [dispatch_as(classmethod)]
    def immediate(klass,seq):
        for item in seq:
            if not item:
                break
        return item


class IfElse(LogicalExpr):
    """Python 2.5 conditional expression"""

    def asFuncAndIds(self,generic):
        argIds = map(generic.getExpressionId, self.argexprs)
        def ifelse(get):
            if get(argIds[1]): return get(argIds[0])
            return get(argIds[2])
        return ifelse, (EXPR_GETTER_ID,)

    [dispatch_as(classmethod)]
    def immediate(klass,seq):
        if seq[1]: return seq[0]
        return seq[2]



class Tuple(ExprBase):
    """Compute an expression by calling a function with an argument tuple"""

    def __new__(klass,function=tuple,*argexprs):
        for arg in argexprs:
            if not isinstance(arg,Const):
                return ExprBase.__new__(klass,function,*argexprs)
        return Const(function([arg.value for arg in argexprs]))

    def __init__(self,function=tuple,*argexprs):
        self.function = function
        self.argexprs = argexprs
        self.hash = hash((type(self),function,argexprs))

    def __eq__(self,other):
        return isinstance(other,Tuple) and \
            (other.function==self.function) and \
            (other.argexprs==self.argexprs)

    def asFuncAndIds(self,generic):
        return lambda *args: self.function(args), tuple(
            map(generic.getExpressionId, self.argexprs)
        )

    def __repr__(self):
        return 'Tuple%r' % (((self.function,)+self.argexprs),)















class Getattr(ExprBase):
    """Compute an expression by calling a function with 0 or more arguments"""

    def __init__(self,ob_expr,attr_name):
        self.ob_expr = ob_expr
        self.attr_name = attr_name
        self.hash = hash((type(self),ob_expr,attr_name))

    def __eq__(self,other):
        return isinstance(other,Getattr) and \
            (other.ob_expr==self.ob_expr) and \
            (other.attr_name==self.attr_name)

    def asFuncAndIds(self,generic):
        return eval("lambda ob: ob.%s" % self.attr_name), (
            generic.getExpressionId(self.ob_expr),
        )


class Const(ExprBase):
    """Compute a 'constant' value"""

    def __init__(self,value):
        self.value = value
        try:
            self.hash = hash((type(self),value))
        except TypeError:
            self.hash = hash((type(self),id(value)))

    def __eq__(self,other):
        return isinstance(other,Const) and (other.value==self.value)

    def asFuncAndIds(self,generic):
        return lambda:self.value,()

    def __repr__(self):
        return 'Const(%r)' % (self.value,)




class Call(ExprBase):

    """Compute an expression by calling a function with 0 or more arguments"""

    def __new__(klass,function,*argexprs):
        if not argexprs:
            return ExprBase.__new__(klass,function)
        for arg in argexprs:
            if not isinstance(arg,Const):
                return ExprBase.__new__(klass)
        return Const(function(*[arg.value for arg in argexprs]))

    def __init__(self,function,*argexprs):
        self.function = function
        self.argexprs = argexprs
        self.hash = hash((type(self),function,argexprs))

    def __eq__(self,other):
        return isinstance(other,Call) and \
            (other.function==self.function) and \
            (other.argexprs==self.argexprs)

    def asFuncAndIds(self,generic):
        return self.function,tuple(map(generic.getExpressionId, self.argexprs))

    def __repr__(self):
        return 'Call%r' % (((self.function,)+self.argexprs),)














class MultiCriterion(AbstractCriterion):
    """Abstract base for boolean combinations of criteria"""
    __slots__ = 'node_type'
    criteria = AbstractCriterion.subject    # alias criteria <-> subject
    enumerable = False

    def __new__(klass,*criteria):
        criteria, all = map(ISeededCriterion,criteria), []
        nt = criteria[0].node_type
        for c in criteria:
            if c.node_type is not nt:
                raise ValueError("Mismatched dispatch types", criteria)
            if c.__class__ is klass:
                # flatten nested criteria
                all.extend([c for c in c.criteria if c not in all])
            elif c not in all:
                all.append(c)
        if len(all)==1:
            return all[0]
        self = object.__new__(klass)
        self.node_type = nt
        AbstractCriterion.__init__(self,frozenset(all))
        return self

    def seeds(self):
        seeds = {}
        for criterion in self.criteria:
            for seed in criterion.seeds():
                seeds[seed]=True
        return seeds.keys()


    def subscribe(self,listener):
        for criterion in self.criteria:
            criterion.subscribe(listener)

    def unsubscribe(listener):
        for criterion in self.criteria:
            criterion.unsubscribe(listener)


    def __repr__(self):
        return '%s%r' % (self.__class__.__name__,tuple(self.criteria))

    def __invert__(self):
        raise NotImplementedError

    def __init__(self,*criteria):
        pass

class AndCriterion(MultiCriterion):
    """All criteria must return true for expression"""
    __slots__ = ()

    def __contains__(self,key):
        for criterion in self.criteria:
            if key not in criterion:
                return False
        return True


class NotCriterion(MultiCriterion):

    __slots__ = ()
    __new__ = AbstractCriterion.__new__

    def __init__(self, criterion):
        criterion = ISeededCriterion(criterion)
        AbstractCriterion.__init__(self,(criterion,))
        self.node_type = criterion.node_type

    def __invert__(self):
        return self.criteria[0]

    def __contains__(self,key):
        return key not in self.criteria[0]


def dispatch_by_truth(table,ob):
    return table.get(bool(ob))


class TruthCriterion(AbstractCriterion):
    """Criterion representing truth or falsity of an expression"""

    __slots__ = ()
    truth = AbstractCriterion.subject

    dispatch_function = staticmethod(dispatch_by_truth)

    def __init__(self,truth=True):
        AbstractCriterion.__init__(self,bool(truth))

    def seeds(self):
        return True,False

    def __contains__(self,key):
        return key==self.truth

    def __invert__(self):
        return TruthCriterion(not self.truth)

    def matches(self,table):
        return self.truth,

    def __repr__(self):
        return "TruthCriterion(%r)" % self.truth


[dispatch.generic()]
def expressionSignature(expr,criterion):
    """Return an ISignature that applies 'criterion' to 'expr'"""

[expressionSignature.when(default)]
def expressionSignature(expr,criterion):
    return Signature([(expr,criterion)])







class CriteriaBuilder:
    bind_globals = True
    simplify_comparisons = True
    mode = TruthCriterion(True)

    def __init__(self,arguments,*namespaces):
        self.expr_builder = ExprBuilder(arguments,*namespaces)

    def mkOp(name):
        op = getattr(ExprBuilder,name)
        def method(self,*args):
            return expressionSignature(op(self.expr_builder,*args), self.mode)
        return method

    for opname in dir(ExprBuilder):
        if opname[0].isalpha() and opname[0]==opname[0].upper():
            locals()[opname] = mkOp(opname)

    def Not(self,expr):
        try:
            self.__class__ = NotBuilder
            return build(self,expr)
        finally:
            self.__class__ = CriteriaBuilder

    _mirror_ops = {
        '>': '<', '>=': '<=', '=>':'<=',
        '<': '>', '<=': '>=', '=<':'>=',
        '<>': '<>', '!=': '<>', '==':'==',
        'is': 'is', 'is not': 'is not'
    }

    _rev_ops = {
        '>': '<=', '>=': '<', '=>': '<',
        '<': '>=', '<=': '>', '=<': '>',
        '<>': '==', '!=': '==', '==':'!=',
        'in': 'not in', 'not in': 'in',
        'is': 'is not', 'is not': 'is'
    }


    def Compare(self,initExpr,((op,other),)):
        left = build(self.expr_builder,initExpr)
        right = build(self.expr_builder,other)

        if isinstance(left,Const) and op in self._mirror_ops:
            left,right,op = right,left,self._mirror_ops[op]

        if isinstance(right,Const):
            if not self.mode.truth:
                op = self._rev_ops[op]

            if op=='in' or op=='not in':
                cond = compileIn(left,right.value,op=='in')
                if cond is not None:
                    return cond
            else:
                if op=='is' or op=='is not':
                    if right.value is None:
                        right = ICriterion(NoneType)
                    else:
                        right = ICriterion(Pointer(right.value))
                    if op=='is not':
                        right = ~right
                else:
                    right = Inequality(op,right.value)
                return Signature([(left, right)])

        # Both sides involve variables or an un-optimizable constant,
        #  so it's a generic boolean criterion  :(
        return expressionSignature(
            self.expr_builder.Compare(initExpr,((op,other),)), self.mode
        )

    def And(self,items):
        return reduce(operator.and_,[build(self,expr) for expr in items])

    def Or(self,items):
        return reduce(operator.or_,[build(self,expr) for expr in items])



def compileIn(expr,criterion,truth):
    """Return a signature or predicate (or None) for 'expr in criterion'"""
    try:
        iter(criterion)
    except TypeError:
        return applyCriterion(expr,criterion,truth)

    if truth:
        return or_criteria(expr,[Inequality('==',v) for v in criterion])
    else:
        return and_criteria(expr,[Inequality('<>',v) for v in criterion])

[dispatch.on('criterion')]
def applyCriterion(expr,criterion,truth):
    """Apply 'criterion' to 'expr' (ala 'expr in criterion') -> sig or pred"""


[applyCriterion.when(ICriterion)]
def applyICriterion(expr,criterion,truth):
    if not truth:
        criterion = ~criterion
    return Signature([(expr,criterion)])


[applyCriterion.when(object)]
def applyDefault(expr,criterion,truth):
    return None     # no special application possible

def or_criteria(expr,seq):
    seq = [Signature([(expr,v)]) for v in seq]
    if len(seq)==1:
        return seq[0]
    return Predicate(seq)

def and_criteria(expr,seq):
    it = iter(seq)
    for val in it: break
    else: raise ValueError("No criteria supplied!")
    for next in it: val &= next
    return Signature([(expr,val)])

class NotBuilder(CriteriaBuilder):

    mode = TruthCriterion(False)

    def Not(self,expr):
        try:
            self.__class__ = CriteriaBuilder
            return build(self,expr)
        finally:
            self.__class__ = NotBuilder

    # Negative logic for and/or
    And = CriteriaBuilder.Or
    Or  = CriteriaBuilder.And



























def _yield_tuples(ob):
    if isinstance(ob,tuple):
        for i1 in ob:
            for i2 in _yield_tuples(i1):
                yield i2
    else:
        yield ob

[expressionSignature.when(
    # matches 'isinstance(expr,Const)'
    "expr in Call and expr.function is isinstance"
    " and len(expr.argexprs)==2 and expr.argexprs[1] in Const"
)]
def convertIsInstanceToClassCriterion(expr,criterion):

    seq = _yield_tuples(expr.argexprs[1].value)
    expr = expr.argexprs[0]

    if not criterion.truth:
        return and_criteria(expr,[~ICriterion(cls) for cls in seq])

    return or_criteria(expr,map(ICriterion,seq))


[expressionSignature.when(
    # matches 'issubclass(expr,Const)'
    "expr in Call and expr.function is issubclass"
    " and len(expr.argexprs)==2 and expr.argexprs[1] in Const"
)]
def convertIsSubclassToSubClassCriterion(expr,criterion):

    seq = _yield_tuples(expr.argexprs[1].value)
    expr = expr.argexprs[0]

    if not criterion.truth:
        return and_criteria(expr,[~SubclassCriterion(cls) for cls in seq])

    return or_criteria(expr,map(SubclassCriterion,seq))



