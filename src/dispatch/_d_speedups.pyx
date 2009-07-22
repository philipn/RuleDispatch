"""C Speedups for commonly-used operations"""

__all__ = [
]

cdef object InstanceType, NoApplicableMethods, DispatchError, _NF, __nclass
from dispatch.interfaces import NoApplicableMethods, DispatchError
from types import InstanceType
__nclass = "__class__"
__nbases = "__bases__"

_NF = [0,None, NoApplicableMethods(), (None,None)]





























cdef extern from "Python.h":
    int PyType_Check(object ob)
    int PyClass_Check(object ob)
    int PyInstance_Check(object ob)
    int PyObject_TypeCheck(object ob, object tp)
    int PyObject_IsInstance(object inst, object cls)
    int PyErr_ExceptionMatches(void *exc)

    void *PyExc_AttributeError
    void *PyObject_GetAttr(object ob, object attr)
    void PyErr_Clear()

    object PyString_InternFromString(char *v)
    object PyMethod_New(object func, object self, object cls)

    ctypedef struct PyTupleObject:
        void *ob_item   # we don't use this, but we can't use 'pass' here

    ctypedef struct PyListObject:
        void *ob_item   # we don't use this, but we can't use 'pass' here

    ctypedef struct PyTypeObject:
        PyTupleObject *tp_bases
        PyTupleObject *tp_mro

    ctypedef struct PyObject:
        PyTypeObject *ob_type

    ctypedef struct PyClassObject:
        PyTupleObject *cl_bases

    ctypedef struct PyInstanceObject:
        PyClassObject *in_class

    int PyObject_IsSubclass(PyClassObject *derived, object cls)
    int PyList_Append(PyListObject *list, object item) except -1
    int PyTuple_GET_SIZE(PyTupleObject *p)
    int PyList_GET_SIZE(PyListObject *p)
    int PyTuple_Check(object op)
    int PyList_Check(object op)

    int len "PyObject_Length" (object o) except -1
    object type "PyObject_Type" (object o)
    int isinstance "PyObject_IsInstance" (object inst, object cls)

    # These macros return borrowed references, so we make them void *
    # When Pyrex casts them to objects, it will incref them
    void * PyTuple_GET_ITEM(PyTupleObject *p, int pos)
    void * PyList_GET_ITEM(PyListObject *p, int pos)
    void * PyDict_GetItem(object dict,object key)
    int PyDict_Check(object op)

    PyTypeObject PyInstance_Type
    PyTypeObject PyBaseObject_Type

    void Py_DECREF(PyObject *p)
    object __Pyx_GetExcValue()

























cdef class _ExtremeType:     # Courtesy of PEP 326

    cdef int _cmpr
    cdef object _rep

    def __init__(self, cmpr, rep):
        self._cmpr = cmpr
        self._rep = rep

    def __hash__(self):
        return object.__hash__(self)

    def __cmp__(self, other):
        if type(other) is type(self) and (<_ExtremeType>other)._cmpr==self._cmpr:
            return 0
        return self._cmpr

    def __repr__(self):
        return self._rep

    def __richcmp__(_ExtremeType self, other, int op):
        if type(other) is type(self) and (<_ExtremeType>other)._cmpr==self._cmpr:
            cmp = 0
        else:
            cmp = self._cmpr
        if op==0:
            return cmp<0
        elif op==1:
            return cmp<=0
        elif op==2:
            return cmp==0
        elif op==3:
            return cmp!=0
        elif op==4:
            return cmp>0
        elif op==5:
            return cmp>=0

Max = _ExtremeType(1, "Max")
Min = _ExtremeType(-1, "Min")

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


def dispatch_by_inequalities(table,ob):

    cdef int lo, hi, mid
    cdef void *tmp

    key = ob,ob
    tmp = PyDict_GetItem(table,key)
    if tmp:
        return <object>tmp
    else:
        tmp = PyDict_GetItem(table,None)
        if tmp:
            ranges = <object>tmp
        else:
            table[None] = ranges = concatenate_ranges(table)

        lo = 0
        hi = len(ranges)
        while lo<hi:
            mid = (lo+hi)/2
            t = <object> PyList_GET_ITEM(<PyListObject *> ranges,mid)
            if ob < <object> PyTuple_GET_ITEM(<PyTupleObject *> t,0):
                hi = mid
            elif ob > <object> PyTuple_GET_ITEM(<PyTupleObject *> t,1):
                lo = mid+1
            else:
                return table[t]


def dispatch_by_mro(table,ob):
    """Lookup '__class__' of 'ob' in 'table' using its MRO order"""

    cdef int bc
    cdef void *tmp
    cdef PyTupleObject *bases

    if not PyDict_Check(table):
        raise TypeError("Not a dict subclass", table)

    tmp = PyObject_GetAttr(ob, __nclass)
    if tmp:
        klass = <object> tmp
        Py_DECREF(<PyObject *>tmp)  # GetAttr does an INCREF

    elif PyErr_ExceptionMatches(PyExc_AttributeError):
        # Some object have no __class__; use their type
        PyErr_Clear()
        klass = type(ob)
    else:
        # Some other error, pass it on up the line
        err = __Pyx_GetExcValue()
        raise

    while 1:
        tmp = PyDict_GetItem(table, klass)
        if tmp:
            return <object>tmp
        if PyClass_Check(klass):
            bases = (<PyClassObject *>klass).cl_bases
        elif PyType_Check(klass):
            bases = (<PyTypeObject *>klass).tp_bases
        else:
            bases = NULL
            tmp = PyObject_GetAttr(ob, __nbases)
            if tmp:
                bt = <object> tmp
                if PyTuple_Check(bt):
                    bases = <PyTupleObject *> tmp
                bt = None

        if not bases:
            raise TypeError("Not a class or type:", klass)

        bc = PyTuple_GET_SIZE(bases)
        if bc>1:
            # Fixup for multiple inheritance
            return table.reseed(klass)
        elif bc:
            klass = <object> PyTuple_GET_ITEM(bases, 0)
        else:
            break

    if PyInstance_Check(ob):
        tmp = PyDict_GetItem(table, InstanceType)
        if tmp:
            return <object>tmp

    if <PyTypeObject *>klass != &PyBaseObject_Type:
        tmp = PyDict_GetItem(table, <object>&PyBaseObject_Type)
        if tmp:
            return <object>tmp




















cdef class ExprCache:

    cdef object cache,argtuple,expr_defs

    def __init__(self,argtuple,expr_defs):
        self.argtuple = argtuple
        self.expr_defs = expr_defs
        self.cache = {}

    def __getitem__(self,item):
        if item==-1:  #EXPR_GETTER_ID:
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

















cdef class BaseDispatcher:

    def __getitem__(self,argtuple):

        assert PyTuple_Check(argtuple)

        cdef int expr,argct
        argct = len(argtuple)
        node = self._dispatcher or self._startNode() or _NF

        factory = <object>PyList_GET_ITEM(<PyListObject *>node,1)
        func = <object>PyList_GET_ITEM(<PyListObject *>node,2)

        while factory is not None:

            if func is None:
                self._acquire()
                try:
                    if node[2] is None:
                        node[2] = func = factory(
                            *<object>PyList_GET_ITEM(<PyListObject *>node,3)
                        )
                finally:
                    self._release()

            expr = <object>PyList_GET_ITEM(<PyListObject *>node,0)
            if expr<argct:
                node = func(
                    <object>PyTuple_GET_ITEM(<PyTupleObject *>argtuple,expr)
                ) or _NF
                factory = <object>PyList_GET_ITEM(<PyListObject *>node,1)
                func = <object>PyList_GET_ITEM(<PyListObject *>node,2)









            else:
                cache = ExprCache(argtuple,self.expr_defs)
                try:
                    node = func(cache[expr]) or _NF
                    factory = <object>PyList_GET_ITEM(<PyListObject *>node,1)
                    func = <object>PyList_GET_ITEM(<PyListObject *>node,2)
                    while factory is not None:
                        if func is None:
                            self._acquire()
                            try:
                                if node[2] is None:
                                    node[2] = func = factory(
                                        *<object>PyList_GET_ITEM(<PyListObject *>node,3)
                                    )
                            finally:
                                self._release()
                        expr = <object>PyList_GET_ITEM(<PyListObject *>node,0)
                        if expr<argct:
                            node = func(
                                <object>PyTuple_GET_ITEM(<PyTupleObject *>argtuple,expr)
                            ) or _NF
                        else:
                            node = func(cache[expr]) or _NF

                        factory = <object>PyList_GET_ITEM(<PyListObject *>node,1)
                        func = <object>PyList_GET_ITEM(<PyListObject *>node,2)

                    break

                finally:
                    cache = None    # GC of values computed during dispatch

        if isinstance(func,DispatchError):
            func(*argtuple)

        return func





