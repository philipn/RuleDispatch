"""Generic function implementations"""

from __future__ import generators
from dispatch.interfaces import *

import protocols, inspect, sys, dispatch
from peak.util.decorators import decorate_assignment, frameinfo, decorate_class
from protocols.interfaces import allocate_lock
from new import instancemethod
from types import FunctionType, ClassType, InstanceType
ClassTypes = (ClassType, type)

__all__ = [
    'GenericFunction', 'Dispatcher', 'AbstractGeneric',
]

_NF = (0,None, NoApplicableMethods(), (None,None))


try:
    frozenset
except NameError:
    from sets import ImmutableSet as frozenset


















def _mkGeneric(oldfunc,argname):
    funcname = oldfunc.__name__
    args, varargs, kwargs, defaults = inspect.getargspec(oldfunc)
    if defaults:
        tmpd = ["=__gfDefaults[%s]" % i for i in range(len(defaults))]
    else:
        tmpd = None

    argspec = inspect.formatargspec(
        args, varargs, kwargs, tmpd, formatvalue=lambda x:x)
    outargs = inspect.formatargspec(args,varargs,kwargs)

    protocol = protocols.Protocol()
    d={}
    s= """
def setup(__gfProtocol, __gfDefaults):

    def %(funcname)s%(argspec)s:
         __gfWhat = __gfProtocol(%(argname)s,None)
         if __gfWhat is None:
             raise NoApplicableMethods(%(argname)s)
         else:
             %(argname)s = __gfWhat[0]
             return __gfWhat[1]%(outargs)s


    return %(funcname)s
""" % locals()
    exec s in globals(),d; func = d['setup'](protocol,defaults)

    def when(cond):
        """Add following function to this GF, using 'cond' as a guard"""
        def callback(frm,name,value,old_locals):
            declarePredicate(cond, protocol, lambda ob: (ob,value))
            if old_locals.get(name) is func:
                return func
            return value
        return decorate_assignment(callback)



    def addMethod(cond,func):
        """Use 'func' when dispatch argument matches 'cond'"""
        declarePredicate(cond, protocol, lambda ob: (ob,func))

    def clone():
        """Return a simple generic function that "inherits" from this one"""
        f = _mkGeneric(oldfunc,argname)
        protocols.declareAdapter(
            protocols.NO_ADAPTER_NEEDED,[f.protocol],forProtocols=[protocol]
        )
        return f

    func.addMethod = addMethod
    func.when      = when
    func.clone     = clone
    func.protocol  = protocol
    func.__doc__   = oldfunc.__doc__
    protocols.adviseObject(func,provides=[IExtensibleFunction])
    return func






















# Bootstrap SimpleGeneric declaration helper function -- itself a SimpleGeneric

[dispatch.on('ob')]
def declarePredicate(ob,proto,factory):
    """Declare a SimpleGeneric dispatch predicate"""

declarePredicate = _mkGeneric(declarePredicate,'ob')
proto = declarePredicate.protocol

def declareForType(typ,proto,factory):
    protocols.declareAdapter(factory,provides=[proto],forTypes=[typ])

def declareForProto(pro,proto,factory):
    protocols.declareAdapter(factory,provides=[proto],forProtocols=[pro])

def declareForSequence(seq,proto,factory):
    for item in seq: declarePredicate(item,proto,factory)

declareForType(ClassType, proto, lambda ob:(ob,declareForType))
declareForType(type,      proto, lambda ob:(ob,declareForType))

declareForProto(protocols.IOpenProtocol,proto,
    lambda ob:(ob,declareForProto))

declareForProto(protocols.IBasicSequence,proto,
    lambda ob:(ob,declareForSequence))















class ExprCache(object):

    __slots__ = 'cache','argtuple','expr_defs'

    def __init__(self,argtuple,expr_defs):
        self.argtuple = argtuple
        self.expr_defs = expr_defs
        self.cache = {}

    def __getitem__(self,item):
        if item==EXPR_GETTER_ID:
            return self.__getitem__
        try:
            return self.argtuple[item]
        except IndexError:
            pass
        try:
            return self.cache[item]
        except KeyError:
            pass

        f,args = self.expr_defs[item]
        f = self.cache[item] = f(*map(self.__getitem__,args))
        return f

















class BaseDispatcher:
    def __getitem__(self,argtuple):
        argct = self.argct
        node = self._dispatcher or self._startNode() or _NF
        expr, factory, func, init = node
        while factory:
            if func is None:
                self._acquire()
                try:
                    if node[2] is None: node[2] = func = factory(*init)
                finally:
                    self._release()
            if expr<argct:
                expr, factory, func, init = node = \
                    func(argtuple[expr]) or _NF
            else:
                cache = ExprCache(argtuple,self.expr_defs)
                try:
                    expr, factory, func, init = node = \
                        func(cache[expr]) or _NF
                    while factory:
                        if func is None:
                            self._acquire()
                            try:
                                if node[2] is None:
                                    node[2] = func = factory(*init)
                            finally:
                                self._release()
                        if expr<argct:
                            expr, factory, func, init = node = \
                                func(argtuple[expr]) or _NF
                        else:
                            expr, factory, func, init = node = \
                                func(cache[expr]) or _NF
                    break
                finally:
                    cache = None    # GC of values computed during dispatch
        if isinstance(func,DispatchError):
            func(*argtuple)
        return func

try:
    from dispatch._d_speedups import BaseDispatcher
except ImportError:
    pass    # '''





































class Dispatcher(BaseDispatcher):
    """Extensible multi-dispatch mapping object"""

    protocols.advise(instancesProvide=[IDispatcher])

    def __init__(self,args):
        self.args = args
        self.argct = len(args)
        global strategy; import strategy
        self.argMap = dict([(name,strategy.Argument(name=name)) for name in args])
        lock = self._lock = allocate_lock()
        self._acquire = lock.acquire
        self._release = lock.release
        self.clear()


    def clear(self):
        self._acquire()
        try:
            self._clear()
        finally:
            self._release()


    def _clear(self):
        self.dirty = False
        self.cases = []
        self.disp_indexes = {}
        self.expr_map = {}
        self._dispatcher = None
        self.constraints=strategy.TGraph()
        self._setupArgs()


    def parse(self,expr_string,local_dict,global_dict):
        from dispatch.predicates import CriteriaBuilder
        from dispatch.ast_builder import parse_expr
        builder=CriteriaBuilder(self.argMap,local_dict,global_dict,__builtins__)
        return parse_expr(expr_string,builder)


    def _build_dispatcher(self, memo=None, disp_ids=None, cases=None):
        if memo is None:
            self._rebuild_indexes()
            cases = frozenset(range(len(self.cases)))
            disp_ids = tuple(self.disp_indexes)
            memo = {}

        if not isinstance(cases,frozenset):
            cases = frozenset(cases)
        if not cases:
            disp_ids = ()   # Skip further analysis, if it comes down to empty

        key = (cases, disp_ids)
        if key in memo:
            return memo[key]
        elif not disp_ids:
            # No more criteria, so make a leaf node
            cases = list(cases); cases.sort()   # restore original order
            node = [0, None, self.combine([self.cases[n] for n in cases]),None]
        else:
            best_id, remaining_ids = self._best_split(cases,disp_ids)
            build = instancemethod(
                instancemethod(self._build_dispatcher, memo, memo.__class__),
                remaining_ids, remaining_ids.__class__
            )

            if best_id is None:
                # None of our current cases had any meaningful tests on the
                # "best" expression, so don't bother building a dispatch node.
                # Instead, try again with the current expression removed.
                node = build(cases)
            else:
                index = self.disp_indexes[best_id]
                node = [
                    best_id[0], index.mkNode, None,
                    (index, cases, build, self._lock)
                ]

        memo[key] = node
        return node

    def _rebuild_indexes(self):
        if self.dirty:
            cases, self.cases = self.cases, []
            self.dirty = False
            for ind in self.disp_indexes.values(): ind.clear()
            map(self._addCase, cases)

    def criterionChanged(self):
        self._acquire()    # XXX could deadlock if called during dispatch
        try:
            self.dirty = True
            self._dispatcher = None
        finally:
            self._release()

    def _setupArgs(self):
        self.expr_defs = [None]*self.argct  # skip defs for arguments
        for p,n in enumerate(self.args):
            self.expr_map[strategy.Argument(name=n)] = p
            self.expr_map[strategy.Argument(pos=p)] = p
            self.expr_map[strategy.Argument(name=n,pos=p)] = p

    def _startNode(self):
        self._acquire()
        try:
            if self._dispatcher is None:
                self._dispatcher = self._build_dispatcher()
            return self._dispatcher
        finally:
            self._release()

    def _addCase(self,case):
        case_num = len(self.cases)
        for disp_id, criterion in case[0].items():
            self.disp_indexes[disp_id][criterion] = case_num

        self.cases.append(case)
        self._dispatcher = None



    def __setitem__(self,signature,method):
        """Update indexes to include 'signature'->'method'"""
        cond = self.parseRule(signature)
        if cond is not None:
            for signature in IDispatchPredicate(cond):
                self[signature] = method
            return

        self._acquire()
        try:
            signature = strategy.Signature(
                [(self._dispatch_id(expr,criterion),criterion)
                    for expr,criterion in ISignature(signature).items()
                        if criterion is not strategy.NullCriterion
                ]
            )
            self._addCase((signature, method))
            self._addConstraints(signature)
        finally:
            self._release()


    [dispatch.on('rule')]
    def parseRule(self,rule,frame=None,depth=3):
        """Parse 'rule' if it's a string/unicode, otherwise return 'None'"""

    [parseRule.when([str,unicode])]
    def parseRule(self,rule,frame,depth):
        frame = frame or sys._getframe(depth)
        return self.parse(rule, frame.f_locals, frame.f_globals)

    [parseRule.when(object)]
    def parseRule(self,rule,frame,depth):
        return None

    def combine(self,cases):
        return strategy.single_best(cases)




    def _best_split(self, cases, disp_ids):
        """Return best (disp_id,method_map,remaining_ids) for current subtree"""

        best_id = None
        best_map = None
        best_spread = None
        remaining_ids = list(disp_ids)
        active_cases = len(cases)
        disabled = self.constraints.successors(remaining_ids)
        skipped = []
        to_do = remaining_ids[:]

        for disp_id in to_do:
            if disp_id in disabled:
                # Skip criteria that have unchecked prerequisites
                skipped.append(disp_id)
                continue

            index = self.disp_indexes[disp_id]
            lindex, total_cases = index.count_for(cases)

            if total_cases == active_cases * lindex:
                # None of the index keys for this expression eliminate any
                # cases, so this expression isn't needed for dispatching
                remaining_ids.remove(disp_id)
                disabled = self.constraints.successors(remaining_ids)
                to_do.extend(skipped); skipped=[]
                continue

            spread = float(total_cases) / lindex
            if spread < best_spread or best_spread is None:
                best_spread = spread
                best_id = disp_id

        if best_id is not None:
            remaining_ids.remove(best_id)

        return best_id, tuple(remaining_ids)



    def _dispatch_id(self,(expr,disp_func),criterion):
        """Replace expr/criterion with a local key"""

        criterion.subscribe(self)
        expr = self.getExpressionId(expr)
        disp = expr, criterion.node_type
        if disp not in self.disp_indexes:
            self.disp_indexes[disp] = criterion.node_type.make_index()
        return expr


    def getExpressionId(self,expr):
        """Replace 'expr' with a local expression ID number"""

        # XXX this isn't threadsafe if not called from 'asFuncAndIds'

        try:
            return self.expr_map[expr]

        except KeyError:
            expr_def = IDispatchableExpression(expr).asFuncAndIds(self)

            try:
                return self.expr_map[expr_def]
            except KeyError:
                expr_id = len(self.expr_defs)
                self.expr_map[expr] = self.expr_map[expr_def] = expr_id
                self.expr_defs.append(expr_def)
                return expr_id


    def _addConstraints(self, signature):
        pre = []
        for key,criterion in signature.items():
            if key[0] >= self.argct:    # constrain non-argument exprs
                for item in pre: self.constraints.add(item,key)
            pre.append(key)




class AbstractGeneric(Dispatcher):

    protocols.advise(instancesProvide=[IGenericFunction])

    delegate = None

    def __init__(self,func):
        self.delegate, args = _mkNormalizer(func, self)
        self.delegate.__dict__ = dict(
            [(k,getattr(self,k))
                for k in dir(self.__class__) if not k.startswith('_')]
        )
        self.delegate.__doc__ = self.__doc__ = func.__doc__
        protocols.adviseObject(self.delegate,[IGenericFunction])
        self.__name__ = func.__name__; self.__call__ = self.delegate
        Dispatcher.__init__(self,args)

    # We can't be used as a method, but make pydoc think we're a callable
    __get__ = None


    def addMethod(self,predicate,function,qualifier=None):
        if qualifier is not None:
            function = qualifier,function
        for signature in IDispatchPredicate(predicate):
            self[signature] = function


    def combine(self,cases):
        raise NotImplementedError(
            "The purpose of this class is to support *custom* method combiners"
        )

    def __call__(__self,*args,**kw):
        return __self.delegate(*args,**kw)






    def _decorate(self,cond,qualifier=None,frame=None,depth=2):   # XXX
        frame = frame or sys._getframe(depth)
        cond = self.parseRule(cond,frame=frame) or cond

        def registerMethod(frm,name,value,old_locals):
            if qualifier is None:
                func = value
            else:
                func = qualifier,value

            kind,module,locals_,globals_ = frameinfo(frm)
            if kind=='class':
                # 'when()' in class body; defer adding the method
                def registerClassSpecificMethod(cls):
                    req = strategy.Signature(
                        [(strategy.Argument(0),ICriterion(cls))]
                    )
                    self.addMethod(req & cond, func)
                    return cls

                decorate_class(registerClassSpecificMethod,frame=frm)
            else:
                self.addMethod(cond,func)

            if old_locals.get(name) in (self,self.delegate):
                return self.delegate

            return value

        return decorate_assignment(registerMethod,frame=frame)











class GenericFunction(AbstractGeneric):

    """Extensible predicate dispatch generic function"""

    def combine(self,cases):
        strict = [strategy.ordered_signatures,strategy.safe_methods]
        loose  = [strategy.ordered_signatures,strategy.all_methods]

        cases = strategy.separate_qualifiers(
            cases,
            around = strict, before = loose, primary = strict, after =loose,
        )

        primary = strategy.method_chain(cases.get('primary',[]))

        if cases.get('after') or cases.get('before'):

            befores = strategy.method_list(cases.get('before',[]))
            afters = strategy.method_list(list(cases.get('after',[]))[::-1])

            def chain(*args,**kw):
                for tmp in befores(*args,**kw): pass  # toss return values
                result = primary(*args,**kw)
                for tmp in afters(*args,**kw): pass  # toss return values
                return result

        else:
            chain = primary

        if cases.get('around'):
            chain = strategy.method_chain(list(cases['around'])+[chain])

        return chain








    def around(self,cond):
        """Add function as an "around" method w/'cond' as a guard

        If 'cond' is parseable, it will be parsed using the caller's frame
        locals and globals.
        """
        return self._decorate(cond,"around")


    def before(self,cond):
        """Add function as a "before" method w/'cond' as a guard

        If 'cond' is parseable, it will be parsed using the caller's frame
        locals and globals.
        """
        return self._decorate(cond,"before")


    def after(self,cond):
        """Add function as an "after" method w/'cond' as a guard

        If 'cond' is parseable, it will be parsed using the caller's frame
        locals and globals.
        """
        return self._decorate(cond,"after")


    def when(self,cond):
        """Add following function to this GF, w/'cond' as a guard

        If 'cond' is parseable, it will be parsed using the caller's frame
        locals and globals.
        """
        return self._decorate(cond)







def _mkNormalizer(func,dispatcher):
    funcname = func.__name__
    if funcname=='<lambda>':
        funcname = "anonymous"

    args, varargs, kwargs, defaults = inspect.getargspec(func)

    if defaults:
        tmpd = ["=__gfDefaults[%s]" % i for i in range(len(defaults))]
    else:
        tmpd = None

    argspec = inspect.formatargspec(
        args, varargs, kwargs, tmpd, formatvalue=lambda x:x)

    allargs = inspect.formatargspec(args,varargs,kwargs)
    outargs = inspect.formatargspec(args, varargs, kwargs,
        formatvarargs=lambda name:name, formatvarkw=lambda name:name,
        join=lambda seq:','.join(seq))
    outargs = outargs[1:-1]+','
    if outargs==',':
        outargs=''
        retargs = []
    else:
        retargs = filter(None,outargs.replace(' ','').split(','))

    d ={}
    s = """
def setup(__dispatcher,__gfDefaults):

    def %(funcname)s%(argspec)s:
        return __dispatcher((%(outargs)s))%(allargs)s

    return %(funcname)s
""" % locals()
    exec s in globals(),d
    return d['setup'](dispatcher.__getitem__,defaults), retargs

defaultNormalize = lambda *__args: __args


