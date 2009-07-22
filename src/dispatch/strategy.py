"""Indexing and Method Combination Strategies

    ProtocolCriterion -- Index handler for checking that an expression adapts
        to a protocol

    ClassCriterion -- Index handler for checking that an expression is of a
        type or class

    SubclassCriterion -- Index handler for checking that an expression is a
        subclass of a given class

    Inequality -- Index handler for checking that an expression has a range
        relation (i.e. <,>,<=,>=,==,!=) to a constant value

    IdentityCriterion -- Index handler for checking that an expression 'is' a
        particular object

    Min, Max -- Extreme values for use with 'Inequality'

    Pointer -- hashable/comparable object pointer, with weakref support, used
        to implement 'IdentityCriterion'

    Predicate, Signature, PositionalSignature, Argument -- primitives to
        implement indexable multiple dispatch predicates

    most_specific_signatures, ordered_signatures, method_chain, method_list,
        all_methods, safe_methods, separate_qualifiers -- utility functions for
        creating method combinations

    validateCriterion -- check if a criterion's implementation is sane
"""










from __future__ import generators
from protocols import Protocol, Adapter, StickyAdapter
from protocols.advice import getMRO
import protocols, operator, inspect
from types import ClassType, InstanceType
ClassTypes = (ClassType, type)
from sys import _getframe, maxint
from weakref import WeakKeyDictionary, ref
from dispatch.interfaces import *
from new import instancemethod
import dispatch
from peak.util.extremes import Min, Max

__all__ = [
    'ProtocolCriterion', 'ClassCriterion', 'SubclassCriterion', 'Inequality',
    'Min', 'Max', 'Predicate', 'Signature', 'PositionalSignature', 'Argument',
    'most_specific_signatures', 'ordered_signatures', 'separate_qualifiers',
    'method_chain', 'method_list', 'all_methods', 'safe_methods', 'Pointer',
    'default', 'IdentityCriterion', 'NullCriterion', 'validateCriterion',
    'DispatchNode', 'SeededIndex',
]

rev_ops = {
    '>': '<=', '>=': '<', '=>': '<',
    '<': '>=', '<=': '>', '=<': '>',
    '<>': '==', '!=': '==', '==':'!='
}

try:
    set
except NameError:
    from sets import Set as set
    from sets import ImmutableSet as frozenset








class SeededIndex(object):
    """Index connecting seeds and results"""

    __slots__ = (
        'dispatch_function', 'allSeeds', 'matchingSeeds', 'criteria',
        'enumerables','impliedSeeds'
    )

    def __init__(self,dispatch_function):
        self.dispatch_function = dispatch_function
        self.clear()

    def clear(self):
        """Reset index to empty"""
        self.allSeeds = {}          # set of all seeds
        self.matchingSeeds = {}     # case -> applicable seeds
        self.criteria = {}          # criterion -> applicable seeds
        self.enumerables = {}       # enumerable -> applicable seeds (reg'd)
        self.impliedSeeds = {}      # enumerable -> applicable seeds (all)






















    def __setitem__(self,criterion,case):
        """Register 'case' under each of the criterion's seeds"""

        if criterion.enumerable:

            enumerables = self.enumerables

            if criterion not in enumerables:

                seed = criterion.leaf_seed
                seeds = self.allSeeds
                new_seed = seed not in seeds
                impliedSeeds = self.impliedSeeds

                for cri in criterion.parent_criteria():
                    if new_seed or cri not in enumerables:
                        impliedSeeds.setdefault(cri,[]).append(seed)

                enumerables[criterion] = impliedSeeds[criterion]

                add = self.addSeed
                for key in criterion.seeds():
                    if key not in seeds: add(key,False)

            self.matchingSeeds[case] = enumerables[criterion]
            return

        criteria = self.criteria

        if criterion not in criteria:
            seeds = self.allSeeds
            add = self.addSeed
            for key in criterion.seeds():
                if key not in seeds: add(key)

            criteria[criterion] = list(criterion.matches(seeds))

        self.matchingSeeds[case] = criteria[criterion]



    def count_for(self,cases):
        """Get the total count of outgoing branches, given incoming cases"""
        get = self.matchingSeeds.get
        dflt = self.allSeeds
        return len(self.allSeeds), sum([len(get(case,dflt)) for case in cases])

    def casemap_for(self,cases):
        """Return a mapping from seeds->caselists for the given cases"""
        get = self.matchingSeeds.get
        dflt = self.allSeeds
        casemap = dict([(key,[]) for key in dflt])
        for case in cases:
            for key in get(case,dflt):
                casemap[key].append(case)
        return casemap

    def addSeed(self,seed, reseed=True):
        """Add a previously-missing seed"""

        if seed in self.allSeeds:
            return  # avoid duping entries if this is a reseed via dispatcher

        for criterion,itsSeeds in self.criteria.items():
            if seed in criterion:
                itsSeeds.append(seed)
        if reseed:
            for criterion,itsSeeds in self.enumerables.items():
                if seed in criterion:
                    itsSeeds.append(seed)
        self.allSeeds[seed] = None

    def mkNode(self,*args):
        node = DispatchNode(*args)
        return instancemethod(self.dispatch_function,node,DispatchNode)







class DispatchNode(dict):

    """A mapping w/lazy population and supporting 'reseed()' operations"""

    protocols.advise(instancesProvide=[IDispatchTable])

    __slots__ = 'index','cases','build','lock'

    def __init__(self, index, cases, build, lock):
        self.index = index
        self.cases = cases
        self.build = build
        self.lock = lock
        dict.__init__(
            self,
            [(key,build(subcases))
                for key,subcases in index.casemap_for(cases).items()]
        )

    def reseed(self,key):
        self.lock.acquire()
        try:
            self.index.addSeed(key)
            self[key] = retval = self.build(
                self.index.casemap_for(self.cases)[key]
            )
            return retval
        finally:
            self.lock.release()

_memo = {}

def make_node_type(dispatch_function):
    if dispatch_function not in _memo:
        class Node(DispatchNode):
            def make_index(cls):
                return SeededIndex(dispatch_function)
            make_index = classmethod(make_index)    # XXX can't use disp.as!
        _memo[dispatch_function] = Node
    return _memo[dispatch_function]

def validateCriterion(criterion, node_type, seeded=True, parents=None):
    """Does 'criterion' have a sane implementation?"""

    criterion = ICriterion(criterion)
    hash(criterion)

    assert criterion.node_type is node_type
    assert criterion==criterion, (criterion, "should equal itself")
    assert criterion!=NullCriterion,(criterion,"shouldn't equal NullCriterion")
    assert criterion!=~criterion,(criterion,"shouldn't equal its inverse")
    assert criterion==~~criterion,(criterion,"should equal its double-inverse")

    assert criterion.implies(NullCriterion), (
        criterion,"should imply NullCriterion"
    )
    assert criterion.implies(criterion), (criterion,"should imply itself")

    assert not (~criterion).implies(criterion), (
        criterion,"should not be implied by its inverse"
    )
    assert not criterion.implies(~criterion), (
        criterion,"should not imply its inverse", ~criterion
    )

    d = {}
    criterion.subscribe(d)
    criterion.unsubscribe(d)

    if seeded:
        criterion = ISeededCriterion(criterion)
        for seed in criterion.seeds():
            d[seed] = seed in criterion

        matches = list(criterion.matches(d))
        for seed in matches:
            assert d[seed], (criterion,"should have contained",seed)
            del d[seed]

        for value in d.values():
            assert not value,(criterion,"should've included",seed,"in matches")

        _parents = set(criterion.parent_criteria())

        if parents is not None:
            # check specific parent assertion
            assert _parents == set(parents), (_parents,set(parents))

        elif criterion.enumerable:
            assert _parents, (
                criterion,"is enumerable and so should have parents"
            )
            assert criterion in _parents, (
                criterion,"does not include itself in its parent criteria"
            )
            assert _parents == set([criterion]), (
                criterion,"has too many parents, or you should be specifying"
                " the `parents` argument to ``validateCriterion()``", _parents
            )

        else:
            assert not _parents, (
                criterion, "is not enumerable and so should not have parents",
                _parents
            )

        for parent in _parents:
            assert criterion.leaf_seed in parent
            assert criterion.implies(parent)














class TGraph:
    """Simple transitive dependency graph"""

    def __init__(self):
        self.data = {}

    def add(self,s,e):
        self.data.setdefault(s,{})
        for old_s,old_es in self.data.items():
            if s in old_es or s is old_s:
                g = self.data.setdefault(old_s,{})
                g[e] = 1
                for ee in self.data.get(e,()):
                    g[ee] = 1

    def items(self):
        """List of current edges"""
        return [(s,e) for s in self.data for e in self.data[s]]

    def successors(self,items):
        """Return a truth map of the acyclic sucessors of 'items'"""
        d = {}
        get = self.data.get
        for s in items:
            for e in get(s,()):
                if s not in get(e,()):
                    d[e] = 1
        return d













def dispatch_by_mro(table,ob):
    """Lookup '__class__' of 'ob' in 'table' using its MRO order"""

    try:
        klass = ob.__class__
    except AttributeError:
        klass = type(ob)

    while True:
        if klass in table:
            return table[klass]
        try:
            klass, = klass.__bases__
        except ValueError:
            if klass.__bases__:
                # Fixup for multiple inheritance
                return table.reseed(klass)
            else:
                break

    if isinstance(ob,InstanceType) and InstanceType in table:
        return table[InstanceType]

    if klass is not object and object in table:
        return table[object]


def dispatch_by_subclass(table,ob):
    if isinstance(ob,ClassTypes):
        while 1:
            if ob in table:
                return table[ob]
            try:
                ob, = ob.__bases__
            except ValueError:
                if ob.__bases__:
                    return table.reseed(ob)
                break
    return table[None]


class AbstractCriterion(object):
    """Common behaviors for typical criteria"""

    class __metaclass__(type):
        def __init__(cls,name,bases,cdict):
            if 'dispatch_function' in cdict:
                cls.node_type = make_node_type(cls.dispatch_function)

    __slots__ = 'hash','subject'
    enumerable = True
    protocols.advise(instancesProvide=[ISeededCriterion])

    def __init__(self,subject=None):
        self.subject = subject
        self.hash = hash(subject)

    def __eq__(self,other):
        return type(self) is type(other) and self.subject==other.subject

    def __ne__(self,other):
        return not self==other

    def matches(self,table):
        for key in table:
            if key in self:
                yield key

    def __invert__(self):
        from predicates import NotCriterion
        return NotCriterion(self)

    def subscribe(self,listener):
        pass

    def unsubscribe(self,listener):
        pass

    def __contains__(self,key):
        raise NotImplementedError


    def __and__(self,other):
        from predicates import AndCriterion
        return AndCriterion(self,other)

    def implies(self,other):
        other = ISeededCriterion(other)
        if self.enumerable:
            return self.leaf_seed in other

        for seed in self.seeds():
            if seed in self and seed not in other:
                return False
        for seed in other.seeds():
            if seed in self and seed not in other:
                return False
        return True

    def parent_criteria(self):
        if self.enumerable:
            yield self


# Alias subject -> leaf_seed by default
AbstractCriterion.leaf_seed = AbstractCriterion.subject


# Hack to make hashing faster, by bypassing function call and attr lookup
AbstractCriterion.__hash__ = instancemethod(
    AbstractCriterion.hash.__get__, None, AbstractCriterion
)


try:
    from _d_speedups import dispatch_by_mro
except ImportError:
    pass





class ClassCriterion(AbstractCriterion):
    """Criterion that indicates expr is of a particular class"""

    __slots__ = ()

    protocols.advise(
        instancesProvide=[ISeededCriterion], asAdapterForTypes=ClassTypes
    )

    dispatch_function = staticmethod(dispatch_by_mro)

    def __init__(self,cls):
        AbstractCriterion.__init__(self,cls)

    def seeds(self):
        return [self.subject,object]

    def __contains__(self,ob):
        if isinstance(ob,ClassTypes):
            return (
                self.subject is object
                or issubclass(ob,self.subject)
                or (self.subject is InstanceType and isinstance(ob,ClassType))
            )
        return False

    def __repr__(self):
        return self.subject.__name__

    def parent_criteria(self):
        for cls in getMRO(self.subject,True):
            yield self.__class__(cls)









_guard = object()

class Pointer(int):

    __slots__ = 'ref'

    def __new__(cls,ob):
        self = Pointer.__base__.__new__(cls,id(ob)&maxint)
        try:
            self.ref=ref(ob)
        except TypeError:
            self.ref=lambda ob=ob: ob
        return self

    def __eq__(self,other):
        return self is other or int(self)==other and self.ref() is not None

    def __repr__(self):
        if self.ref() is None:
            return "Pointer(<invalid at 0x%s>)" % hex(self)
        else:
            return "Pointer(%r)" % self.ref()


def dispatch_by_identity(table,ob):
    oid = id(ob)&maxint
    if oid in table:
        return table[oid]
    return table[None]












class IdentityCriterion(AbstractCriterion):
    """Criterion that is true when target object is the same"""

    protocols.advise(
        instancesProvide=[ISeededCriterion],asAdapterForTypes=[Pointer]
    )
    __slots__ = ()
    dispatch_function = staticmethod(dispatch_by_identity)

    def __init__(self,ptr):
        AbstractCriterion.__init__(self,ptr)

    def seeds(self):
        return None,self.subject

    def matches(self,table):
        return self.subject,

    def __contains__(self,ob):
        return ob==self.subject

    def __repr__(self):
        return `self.subject`


class NullCriterion(AbstractCriterion):
    """A "wildcard" Criterion that is always true"""

    node_type = None

    def seeds(self):            return ()
    def __contains__(self,ob):  return True
    def implies(self,other):    return False
    def __repr__(self):         return "NullCriterion"
    def matches(self,table):    return list(table)

NullCriterion = NullCriterion()




class SubclassCriterion(ClassCriterion):
    """Criterion that indicates expr is a subclass of a particular class"""

    __slots__ = ()

    dispatch_function = staticmethod(dispatch_by_subclass)

    def seeds(self):
        return [self.subject,None]

    def __repr__(self):
        return "SubclassCriterion(%s)" % (self.subject.__name__,)





























def dispatch_by_inequalities(table,ob):
    key = ob,ob
    try:
        return table[key]
    except KeyError:
        if None not in table:
            table[None] = ranges = concatenate_ranges(table)
        else:
            ranges = table[None]
        lo = 0; hi = len(ranges)
        while lo<hi:
            mid = (lo+hi)//2;  tl,th = ranges[mid]
            if ob<tl:
                hi = mid
            elif ob>th:
                lo = mid+1
            else:
                return table[ranges[mid]]

def concatenate_ranges(range_map):
    ranges = range_map.keys(); ranges.sort()
    output = []
    last = Min
    for (l,h) in ranges:
        if l<last or l==h:
            continue
        output.append((l,h))
        last = h
    return output

try:
    from _d_speedups import \
        concatenate_ranges, dispatch_by_inequalities, Min, Max
except ImportError:
    pass






class InequalityIndex(SeededIndex):

    __slots__ = ('last_cases','last_out')

    dispatch_function = staticmethod(dispatch_by_inequalities)

    def __init__(self):
        self.clear()


    def count_for(self,cases):
        """Get the total count of outgoing branches, given incoming cases"""
        casemap = self.casemap_for(cases)
        return len(casemap), sum([len(x) for x in casemap.itervalues()])

    def clear(self):
        """Reset index to empty"""
        self.allSeeds = {}            # set of all seeds
        self.criteria = {}            # criterion -> applicable seeds
        self.last_cases = None
        self.last_out = None

    def __setitem__(self,criterion,case):
        """Register 'case' under each of the criterion's seeds"""
        self.criteria[case] = criterion
        for (lo,hi) in criterion.ranges:
            self.allSeeds[lo] = self.allSeeds[hi] = None

    def addSeed(self,seed):
        raise NotImplementedError











    def casemap_for(self,cases):
        """Return a mapping from seeds->caselists for the given cases"""
        if cases is self.last_cases or cases==self.last_cases:
            return self.last_out
        tmp = {}
        out = {}
        get = self.criteria.get
        all = Inequality('..',[(Min,Max)])
        have_ineq = False
        for case in cases:
            for (lo,hi) in get(case,all).ranges:
                if lo not in tmp:
                    tmp[lo] = [],[],[]
                if lo==hi:
                    tmp[lo][2].append(case)
                else:
                    have_ineq = True
                    if hi not in tmp:
                        tmp[hi] = [],[],[]
                    tmp[lo][0].append(case)
                    if hi is not Max: tmp[hi][1].append(case)
        if have_ineq:
            keys = tmp.keys()
            keys.sort()
            current = frozenset(tmp.get(Min,[[]])[0])
            hi = Min
            for val in keys:
                add,remove,eq = tmp[val]
                lo,hi = hi,val
                out[lo,hi] = current
                current = current.difference(remove)
                out[val,val] = current.union(eq)
                current = current.union(add)
        else:
            out[Min,Max] = []   # default
            for val,(add,remove,eq) in tmp.items():
                out[val,val] = eq
        self.last_out = out
        self.last_cases = cases
        return out

class Inequality(object):
    """Criterion that indicates target matches specified const. inequalities"""

    __slots__ = 'hash','ranges'
    protocols.advise(instancesProvide=[ICriterion])

    class node_type(DispatchNode):
        make_index = InequalityIndex

    def __init__(self,op,val):
        ranges = []
        if op=='..':
            ranges.extend(val)
        else:
            if op=='!=':
                op = '<>'   # easier to process this way
            if '<' in op:  ranges.append((Min,val))
            if '=' in op:  ranges.append((val,val))
            if '>' in op:  ranges.append((val,Max))
            if not ranges or [c for c in op if c not in '<=>']:
                raise ValueError("Invalid inequality operator", op)

        self.ranges = ranges = tuple(ranges)
        self.hash = hash(ranges)


    def implies(self,other):
        for r in self.ranges:
            if not r in other:
                return False
        return True


    def __repr__(self):
        return 'Inequality("..",%r)' % (self.ranges,)






    def __contains__(self,ob):
        for r in self.ranges:
            if ob==r:
                return True
            elif ob[0]==ob[1]:  # single point must be *inside* the range
                if ob[0]>r[0] and ob[1]<r[1]:
                    return True
            elif ob[0]>=r[0] and ob[1]<=r[1]:   # for range, overlap allowed
                return True
        return False

    def __and__(self, other):
        ranges = []
        for r in self.ranges:
            if r in other:
                ranges.append(r)
            else:
                l1, h1 = r
                for l2,h2 in other.ranges:
                    if l2>h1 or h2<l1:
                        break
                    l = max(l1,l2)
                    h = min(h1,h2)
                    if l<=h:
                        ranges.append((l,h))
                        l1 = l
        return self.__class__('..',ranges)

    def __eq__(self,other):
        return type(self) is type(other) and self.ranges==other.ranges

    def __ne__(self,other):
        return not self==other

    def subscribe(self,listener):
        pass

    def unsubscribe(self,listener):
        pass


    def __invert__(self):
        ranges = {}
        last = Min
        for lo,hi in self.ranges:
            if lo<>Min and (last,lo) not in self:
                ranges[last,lo] = 1
            last = hi
            if lo<>hi and lo<>Min and (lo,lo) not in self:
                ranges[lo,lo] = 1
        if last is not Max:
            if (last,last) not in self:
                ranges[last,last]=1
            ranges[last,Max]=1
        ranges = list(ranges); ranges.sort()
        return self.__class__('..',ranges)



# Hack to make hashing faster, by bypassing function call and attr lookup
Inequality.__hash__ = instancemethod(
    Inequality.hash.__get__, None, Inequality
)



















class _Notifier(Protocol):

    """Helper class that forwards class registration info"""

    def __init__(self,baseProto):
        Protocol.__init__(self)
        from weakref import WeakKeyDictionary
        self.__subscribers = WeakKeyDictionary()
        baseProto.addImpliedProtocol(self, protocols.NO_ADAPTER_NEEDED, 1)

    def subscribe(self,listener):
        self._Protocol__lock.acquire()
        try:
            self.__subscribers[listener] = 1
        finally:
            self._Protocol__lock.release()

    def unsubscribe(self,listener):
        self._Protocol__lock.acquire()
        try:
            if listener in self.__subscribers:
                del self.__subscriber[listener]
        finally:
            self._Protocol__lock.release()

    def registerImplementation(self,klass,adapter=protocols.NO_ADAPTER_NEEDED,depth=1):
        old_reg = Protocol.registerImplementation.__get__(self,self.__class__)
        result = old_reg(klass,adapter,depth)

        self._Protocol__lock.acquire()

        try:
            if self.__subscribers:
                for subscriber in self.__subscribers.keys():
                    subscriber.criterionChanged()
        finally:
            self._Protocol__lock.release()

        return result


class ProtocolCriterion(StickyAdapter,AbstractCriterion):

    """Criterion that indicates instances of expr's class provide a protocol"""

    protocols.advise(
        instancesProvide=[ISeededCriterion],
        asAdapterForTypes=[Protocol]
    )

    attachForProtocols = (ICriterion,ISeededCriterion)
    dispatch_function  = staticmethod(dispatch_by_mro)

    enumerable = False  # Just to be safe

    def __init__(self,ob):
        self.notifier = _Notifier(ob)
        StickyAdapter.__init__(self,ob)
        AbstractCriterion.__init__(self,ob)

    def subscribe(self,listener):
        self.notifier.subscribe(listener)

    def unsubscribe(self,listener):
        self.notifier.unsubscribe(listener)

    def seeds(self):
        return self.notifier._Protocol__adapters.keys() + [object]

    def __contains__(self,ob):
        if isinstance(ob,ClassTypes):
            bases = self.subject._Protocol__adapters
            for base in getMRO(ob,True):
                if base in bases:
                    return bases[base][0] is not protocols.DOES_NOT_SUPPORT
        return False






    def implies(self,other):

        other = ISeededCriterion(other)

        if other is NullCriterion:
            return True

        for base in self.notifier._Protocol__adapters.keys():
            if base not in other:
                return False

        return True

    def __repr__(self):
        return self.subject.__name__


























def most_specific_signatures(cases):
    """List the most specific '(signature,method)' pairs from 'cases'

    'cases' is a list of '(signature,method)' pairs, where each 'signature'
    must provide 'ISignature'.  This routine checks the implication
    relationships between pairs of signatures, and then returns a shorter list
    of '(signature,method)' pairs such that no other signature from the
    original list implies a signature in the new list.
    """

    if len(cases)==1:
        # Shortcut for common case
        return list(cases)

    best, rest = list(cases[:1]), list(cases[1:])

    for new_sig,new_meth in rest:

        for old_sig, old_meth in best[:]:   # copy so we can modify inplace

            new_implies_old = new_sig.implies(old_sig)
            old_implies_new = old_sig.implies(new_sig)

            if new_implies_old:

                if not old_implies_new:
                    # better, remove the old one
                    best.remove((old_sig, old_meth))

            elif old_implies_new:
                # worse, skip adding the new one
                break
        else:
            # new_sig has passed the gauntlet, as it has not been implied
            # by any of the current "best" items
            best.append((new_sig,new_meth))

    return best



def ordered_signatures(cases):
    """Return list of lists of cases sorted into partial implication order

    Each list within the returned list contains cases whose signatures are
    overlapping, equivalent, or disjoint with one another, but are more
    specific than any other case in the lists that follow."""

    rest = list(cases)

    while rest:
        best = most_specific_signatures(rest)
        map(rest.remove,best)
        yield best


def all_methods(grouped_cases):
    """Yield all methods in 'grouped_cases'"""
    for group in grouped_cases:
        for signature,method in group:
            yield method


def safe_methods(grouped_cases):
    """Yield non-ambiguous methods (plus optional raiser of AmbiguousMethod)"""

    for group in grouped_cases:
        if len(group)>1:
            yield AmbiguousMethod(group)
            break
        for signature,method in group:
            yield method










def method_list(methods):
    """Return callable that yields results of calling 'methods' w/same args"""

    methods = list(methods)     # ensure it's re-iterable

    def combined(*args,**kw):
        for m in methods:
            yield m(*args,**kw)

    return combined


def method_chain(methods):
    """Chain 'methods' such that each may call the next"""

    methods = iter(methods) # ensure that nested calls will see only the tail

    for method in methods:
        try:
            args = inspect.getargspec(method)[0]
        except TypeError:
            return method   # not a function, therefore not chainable

        if args and args[0]=='next_method':
            if getattr(method,'im_self',None) is None:
                next_method = method_chain(methods)
                return instancemethod(method,next_method,type(next_method))

        return method

    return NoApplicableMethods()


def single_best(cases):
    for method in safe_methods(ordered_signatures(cases)):
        return method
    else:
        return NoApplicableMethods()



def separate_qualifiers(qualified_cases, **postprocessors):
    """list[qualified_case] -> dict[qualifier:list[unqualified_case]]

    Turn a list of cases with possibly-qualified methods into a dictionary
    mapping qualifiers to (possibly post-processed) case lists.  If a given
    method is not qualified, it's treated as though it had the qualifier
    '"primary"'.

    Keyword arguments supplied to this function are treated as a mapping from
    qualifiers to lists of functions that should be applied to the list of
    cases to that qualifier.  So, for example, this::

        cases = separate_qualifiers(cases,
            primary=[strategy.ordered_signatures,strategy.safe_methods],
        )

    is equivalent to::

        cases = separate_qualifiers(cases)
        if "primary" in cases:
            cases["primary"]=safe_methods(ordered_signatures(cases["primary"]))

    Notice, by the way, that the postprocessing functions must be listed in
    order of *application* (i.e. outermost last).
    """

    cases = {}
    for signature,method in qualified_cases:
        if isinstance(method,tuple):
            qualifier,method = method
        else:
            qualifier="primary"
        cases.setdefault(qualifier,[]).append((signature,method))

    for k,v in cases.items():
        if k in postprocessors:
            for p in postprocessors[k]:
                v = p(v)
            cases[k] = v
    return cases

class ExprBase(object):

    protocols.advise(instancesProvide=[IDispatchableExpression])

    def __ne__(self,other):
        return not self.__eq__(other)

    def __hash__(self):
        return self.hash

    def asFuncAndIds(self,generic):
        raise NotImplementedError





























class Argument(ExprBase):

    """The most basic kind of dispatch expression: an argument specifier"""

    def __init__(self,pos=None,name=None):
        if pos is None and name is None:
            raise ValueError("Argument name or position must be specified")

        self.pos = pos
        self.name = name
        self.hash = hash((type(self),self.pos,self.name))


    def __eq__(self,other):
        return isinstance(other,Argument) and \
            (other.pos==self.pos) and \
            (other.name==self.name)


    def asFuncAndIds(self,generic):
        raise NameError("%r is not known to %s" % (self,generic))


    def __repr__(self):
        if self.name:
            return self.name
        return 'Argument(%r)' % self.pos














class Predicate(object):
    """A set of alternative signatures in disjunctive normal form"""

    protocols.advise(
        instancesProvide=[IDispatchPredicate],
        asAdapterForProtocols = [protocols.sequenceOf(ISignature)],
    )

    def __init__(self,items):
        self.items = all = []
        for item in map(ISignature,items):
            if item not in all:
                all.append(item)

    def __iter__(self):
        return iter(self.items)

    def __and__(self,other):
        return Predicate(
            [(a & b) for a in self for b in IDispatchPredicate(other)])

    def __or__(self,other):

        sig = ISignature(other,None)

        if sig is not None:
            if len(self.items)==1:
                return self.items[0] | sig
            return Predicate(self.items+[sig])

        return Predicate(list(self)+list(other))

    def __eq__(self,other):
        return self is other or self.items==list(other)

    def __ne__(self,other):
        return not self.__eq__(other)

    def __repr__(self):
        return `self.items`

protocols.declareAdapter(
    lambda ob: Predicate([ob]), [IDispatchPredicate], forProtocols=[ISignature]
)

class Signature(object):
    """A set of criteria (in conjunctive normal form) applied to expressions"""

    protocols.advise(instancesProvide=[ISignature])

    __slots__ = 'data','keys'

    def __init__(self, __id_to_test=(), **kw):
        items = list(__id_to_test)+[(Argument(name=k),v) for k,v in kw.items()]
        self.data = data = {}; self.keys = keys = []
        for k,v in items:
            v = ICriterion(v)
            k = k,v.node_type
            if k in data:
                data[k] &= v
            else:
                data[k] = v; keys.append(k)

    def implies(self,otherSig):
        otherSig = ISignature(otherSig)
        for expr_id,otherCriterion in otherSig.items():
            if not self.get(expr_id).implies(otherCriterion):
                return False
        return True

    def items(self):
        return [(k,self.data[k]) for k in self.keys]

    def get(self,expr_id):
        return self.data.get(expr_id,NullCriterion)

    def __repr__(self):
        return 'Signature(%s)' % (','.join(
            [('%r=%r' % (k,v)) for k,v in self.data.items()]
        ),)


    def __and__(self,other):
        me = self.data.items()
        if not me:
            return other

        if IDispatchPredicate(other) is other:
            return Predicate([self]) & other

        they = ISignature(other).items()
        if not they:
            return self

        return Signature(
            [(k[0],self.data[k]) for k in self.keys] +
            [(k,v) for (k,d),v in they]
        )


    def __or__(self,other):

        me = self.data.items()
        if not me:
            return self  # Always true

        if IDispatchPredicate(other) is other:
            return Predicate([self]) | other

        they = ISignature(other).items()
        if not they:
            return other  # Always true

        return Predicate([self,other])









    def __eq__(self,other):
        if other is self:
            return True

        other = ISignature(other,None)

        if other is None or other is NullCriterion:
            return False

        for k,v in self.items():
            if v!=other.get(k):
                return False

        for k,v in other.items():
            if v!=self.get(k):
                return False

        return True


    def __ne__(self,other):
        return not self.__eq__(other)


class PositionalSignature(Signature):

    protocols.advise(
        instancesProvide=[ISignature],
        asAdapterForProtocols=[protocols.sequenceOf(ICriterion)]
    )

    __slots__ = ()

    def __init__(self,criteria,proto=None):
        Signature.__init__(self,
            zip(map(Argument,range(len(criteria))), criteria)
        )

default = Signature()


