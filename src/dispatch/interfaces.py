from protocols import Interface, Attribute

__all__ = [
    'IDispatchFunction', 'ICriterion', 'ISignature', 'IDispatchPredicate',
    'IDispatcher', 'AmbiguousMethod', 'NoApplicableMethods',
    'IDispatchableExpression', 'IGenericFunction', 'IDispatchTable',
    'EXPR_GETTER_ID','IExtensibleFunction', 'DispatchError',
    'ISeededCriterion',
]

class DispatchError(Exception):
    """A dispatch error has occurred"""

    def __call__(self,*args,**kw):
        raise self.__class__(*self.args+(args,kw))

    def __repr__(self):
        # This method is needed so doctests for 2.3/2.4 match 2.5
        return self.__class__.__name__+repr(self.args)

class AmbiguousMethod(DispatchError):
    """More than one choice of method is possible"""


class NoApplicableMethods(DispatchError):
    """No applicable method has been defined for the given arguments"""


EXPR_GETTER_ID = -1












class ICriterion(Interface):
    """A criterion to be applied to an expression

    A criterion comprises a "node type" (that determines how the
    criterion will be checked, such as an 'isinstance()' check or range
    comparison) and a value or values that the expression must match.  Note
    that a criterion describes only the check(s) to be performed, not the
    expression to be checked."""

    node_type = Attribute(
        """The type of object that will actually do the dispatching"""
    )

    def __and__(other):
        """Apply multiple criteria of the same node type to the same expr"""

    def __hash__():
        """Equal criteria should have equal hashes"""

    def __eq__(other):
        """Return true if equal"""

    def __ne__(other):
        """Return false if equal"""

    def __invert__():
        """Return an inverse version of this criterion (i.e. '~criterion')"""

    def implies(other):
        """Return true if truth of this criterion implies truth of 'other'"""

    def subscribe(listener):
        """Call 'listener.criterionChanged()' if applicability changes

        Multiple calls with the same listener should be treated as a no-op."""

    def unsubscribe(listener):
        """Stop calling 'listener.criterionChanged()'

        Unsubscribing a listener that was not subscribed should be a no-op."""

class ISeededCriterion(ICriterion):
    """A criterion that works with a SeededIndex"""

    enumerable = Attribute(
        """Can criterion enumerate its implications via ``parent_seeds()``?"""
    )

    leaf_seed = Attribute(
        """If ``enumerable``, this must be the most-specific parent seed"""
    )

    def seeds():
        """Return iterable of known-good keys

        The keys returned will be used to build outgoing edges in generic
        functions' dispatch tables, which will be passed to the
        'dispatch_function' for interpretation."""

    def __contains__(key):
        """Return true if criterion is true for 'key'

        This method will be passed each seed provided by this or any other
        criteria with the same 'dispatch_function' that are being applied to
        the same expression."""

    def matches(table):
        """Return iterable of keys from 'table' that this criterion matches"""

    def parent_criteria():
        """Iterable of all the criteria implied by this criterions"""











class IDispatchFunction(Interface):
    """Determine what path to take at a dispatch node, given an expression"""

    def __call__(table,ob):
        """Return entry from 'table' that matches 'ob' ('None' if not found)

        'table' is an 'IDispatchTable' mapping criterion seeds to dispatch
        nodes.  The dispatch function should return the appropriate entry from
        the dictionary."""

    def __eq__(other):
        """Return true if equal"""

    def __ne__(other):
        """Return false if equal"""

    def __hash__():
        """Return hashcode"""























class IDispatchTable(Interface):

    """A dispatch node for dispatch functions to search"""

    def __contains__(key):
        """True if 'key' is in table"""

    def __getitem__(key):
        """Return dispatch node for 'key', or raise 'KeyError'"""

    def reseed(key):
        """Add 'key' to dispatch table and return the node it should have"""


class ISignature(Interface):

    """Ordered mapping from expression id -> criterion that should be applied

    Note that signatures do not/should not interpret expression IDs; the IDs
    may be any object that can be used as a dictionary key.
    """

    def items():
        """Sequence of '((id,disp_func),criterion)' pairs for this signature"""

    def get(expr_id):
        """Return this signature's 'ICriterion' for 'expr_id'"""

    def implies(otherSig):
        """Return true if this signature implies 'otherSig'"""

    def __eq__(other):
        """Return true if equal"""

    def __ne__(other):
        """Return false if equal"""





class IDispatchPredicate(Interface):

    """Sequence of "or"-ed signatures"""

    def __iter__():
        """Iterate over "or"-ed signatures"""

    def __eq__(other):
        """Return true if equal"""

    def __ne__(other):
        """Return false if equal"""


class IDispatchableExpression(Interface):

    """Expression definition suitable for dispatching"""

    def asFuncAndIds(generic):
        """Return '(func,idtuple)' pair for expression computation"""

    def __eq__(other):
        """Return true if equal"""

    def __ne__(other):
        """Return false if equal"""

    def __hash__():
        """Return hashcode"""












class IDispatcher(Interface):

    """Multi-dispatch mapping object"""

    def __getitem__(argtuple):
        """Return the rule body (or combo thereof) that matches 'argtuple'"""

    def __setitem__(signature,body):
        """Store 'body' as the rule body for arg tuples matching 'signature'"""


    def parse(expr_string, local_dict, global_dict):
        """Parse 'expr_string' --> ISignature or IDispatchPredicate"""


    def getExpressionId(expr):
        """Return an expression ID for use in 'asFuncAndIds()' 'idtuple'

        Note that the constant 'EXPR_GETTER_ID' may be used in place of calling
        This method, if you want the ID corresponding to a function that will
        return the value of any other expression whose ID is passed to it."""

    def criterionChanged():
        """Notify that a criterion has changed meaning, invalidating indexes"""

    def clear():
        """Empty all signatures, methods, criteria, expressions, etc."""














class IExtensibleFunction(Interface):

    def __call__(*__args,**__kw):
        """Invoke the function and return results"""

    def addMethod(predicate,method):
        """Call 'method' when input matches 'predicate'

        (Note that single and multiple-dispatch functions use different
        predicate types: type/class/sequence vs. 'IDispatchPredicate').
        """

    def when(cond):
        """Add following function to this GF, w/'cond' as a guard

        This is used to add a method to a generic function.  E.g.::

            import foo

            @foo.barFunc.when(XYZ)
            def whatever(x,y,z):
                # code for situation XYZ

        After the execution of this alternate form, 'whatever' will be bound
        to the 'whatever' function as shown, but it will also have been added
        to 'foo.barFunc' under condition 'XYZ'.
        """


class IGenericFunction(IExtensibleFunction, IDispatcher):
    """Extensible function that stores methods in an IDispatcher"""

    # copy() ?








