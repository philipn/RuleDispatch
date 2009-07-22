"""Method combining subclasses of Dispatcher and GenericFunction"""

from strategy import ordered_signatures
from interfaces import AmbiguousMethod
from functions import Dispatcher

class MapDispatcher(Dispatcher):
    """Abstract base class for method combiners that merge metadata

    To use this class, subclass it and override the 'getItems()' method
    (and optionally the 'shouldStop()' method to support your particular kind
    of metadata.  Then use the subclass as a method combiner for a dispatcher
    or generic function.  See 'combiners.txt' for sample code.
    """
    def getItems(self,signature,method):
        """Return an iterable of '(key,value)' pairs for given rule"""
        raise NotImplementedError

    def shouldStop(self,signature,method):
        """Return truth if combining should stop at this precedence level"""

    def combine(self,items):
        """Build a dictionary from a sequence of '(signature,method)' pairs"""
        d = {}
        should_stop = False

        for level in ordered_signatures(items):
            current = {}
            for item in level:
                should_stop = should_stop or self.shouldStop(*item)
                for k,v in self.getItems(*item):
                    if k in d:  # already defined
                        continue
                    if k in current and current[k]<>v:
                        return AmbiguousMethod(k,v,current[k])
                    current[k] = v
            d.update(current)
            if should_stop:
                break
        return d

