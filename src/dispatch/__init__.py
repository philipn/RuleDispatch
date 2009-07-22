"""Multiple/Predicate Dispatch Framework

 This framework refines the algorithms of Chambers and Chen in their 1999
 paper, "Efficient Multiple and Predicate Dispatching", to make them suitable
 for Python, while adding a few other enhancements like incremental index
 building and lazy expansion of the dispatch DAG.   Also, their algorithm
 was designed only for class selection and true/false tests, while this
 framework can be used with any kind of test, such as numeric ranges, or custom
 tests such as categorization/hierarchy membership.

 NOTE: this package is not yet ready for prime-time.  APIs are subject to
 change randomly without notice.  You have been warned!

 TODO

    * Support DAG-walking for visualization, debugging, and ambiguity detection
"""

from dispatch.interfaces import *
from types import ClassType as _ClassType

_cls  = _ClassType,type



















def generic(combiner=None):
    """Use the following function as the skeleton for a generic function

    Decorate a Python function so that it wraps an instance of
    'dispatch.functions.GenericFunction' that has been configured with the
    decorated function's name, docstring, argument signature, and default
    arguments.

    The decorated function will have additional attributes besides those of
    a normal function.  (See 'dispatch.IGenericFunction' for more information
    on these special attributes/methods.)  Most commonly, you will use the
    'when()' method of the decorated function to define "rules" or "methods"
    of the generic function.  For example::

        import dispatch

        @dispatch.generic()
        def someFunction(*args):
            '''This is a generic function'''

        @someFunction.when("len(args)>0")
        def argsPassed(*args):
            print "Arguments were passed!"

        @someFunction.when("len(args)==0")
        def noArgsPassed(*args):
            print "No arguments were passed!"

        someFunction()  # prints "No args passed"
        someFunction(1) # prints "args passed"

    Note that when using older Python versions, you must use
    '[dispatch.generic()]' instead of '@dispatch.generic()'.
    """

    from dispatch.functions import GenericFunction, AbstractGeneric
    from peak.util.decorators import decorate_assignment




    if combiner is None:
        def callback(frm,name,value,old_locals):
            return GenericFunction(value).delegate
    elif isinstance(combiner,_cls) and issubclass(combiner,AbstractGeneric):
        def callback(frm,name,value,old_locals):
            return combiner(value).delegate
    else:
        def callback(frm,name,value,old_locals):
            gf = GenericFunction(value)
            gf.combine = combiner
            return gf.delegate

    return decorate_assignment(callback)


def dispatch_as(*decorators):
    """Use Python 2.4 decorators w/Python 2.2+

    Example:

        import dispatch

        class Foo(object):
            [dispatch.as(classmethod)]
            def something(cls,etc):
                \"""This is a classmethod\"""
    """

    if len(decorators)>1:
        decorators = list(decorators)
        decorators.reverse()

    def callback(frame,k,v,old_locals):
        for d in decorators:
            v = d(v)
        return v

    from peak.util.decorators import decorate_assignment
    return decorate_assignment(callback)


def on(argument_name):
    """Decorate the following function as a single-dispatch generic function

    Single-dispatch generic functions may have a slight speed advantage over
    predicate-dispatch generic functions when you only need to dispatch based
    on a single argument's type or protocol, and do not need arbitrary
    predicates.

    Also, single-dispatch functions do not require you to adapt the dispatch
    argument when dispatching based on protocol or interface, and if the
    dispatch argument has a '__conform__' method, it will attempt to use it,
    rather than simply dispatching based on class information the way
    predicate dispatch functions do.

    The created generic function will use the documentation from the supplied
    function as its docstring.  And, it will dispatch methods based on the
    argument named by 'argument_name', and otherwise keeping the same argument
    signature, defaults, etc.  For example::

        @dispatch.on('y')
        def doSomething(x,y,z):
            '''Doc for 'doSomething()' generic function goes here'''

        @doSomething.when([SomeClass,OtherClass])
        def doSomething(x,y,z):
            # do something when 'isinstance(y,(SomeClass,OtherClass))'

        @doSomething.when(IFoo)
        def doSomething(x,y,z):
            # do something to a 'y' that has been adapted to 'IFoo'
    """

    def callback(frm,name,value,old_locals):
        return _mkGeneric(value,argument_name)

    from dispatch.functions import _mkGeneric
    from peak.util.decorators import decorate_assignment
    return decorate_assignment(callback)



