"""Test generic functions expression parsing"""

from unittest import TestCase, makeSuite, TestSuite
from dispatch import *; from dispatch.functions import *
from dispatch.predicates import *; from dispatch.strategy import *
from dispatch.ast_builder import *
from dispatch import predicates
import operator,sys,types,dispatch
MAXINT = `sys.maxint`

class StringBuilder:

    """Simple parse event receiver to test the AST build functions"""

    def Name(self,name):
        return name

    def Const(self,const):
        return repr(const)

    def Compare(self,initExpr,comparisons):
        data = [build(self,initExpr)]
        for op,val in comparisons:
            data.append(op)
            data.append(build(self,val))
        return 'Compare(%s)' % ' '.join(data)

    def Getattr(self,left,right):
        return 'Getattr(%s,%r)' % (build(self,left), right)

    def Dict(self, items):
        return '{%s}' % ','.join([
            '%s:%s' % (build(self,k),build(self,v)) for k,v in items
        ])

    def Sliceobj(self,start,stop,stride):
        return 'Sliceobj(%s,%s,%s)' % (
            build(self,start),build(self,stop),build(self,stride)
        )


    def mkBinOp(op):
        pat = '%s(%%s,%%s)' % op
        def method(self,left,right):
            return pat % (build(self,left),build(self,right))
        return method

    def multiOp(fmt,sep=','):
        def method(self,items):
            return fmt % sep.join([build(self,item) for item in items])
        return method

    def unaryOp(fmt):
        def method(self,expr):
            return fmt % build(self,expr)
        return method

    UnaryPlus  = unaryOp('Plus(%s)')
    UnaryMinus = unaryOp('Minus(%s)')
    Invert     = unaryOp('Invert(%s)')
    Backquote  = unaryOp('repr(%s)')
    Not        = unaryOp('Not(%s)')
    And        = multiOp('And(%s)')
    Or         = multiOp('Or(%s)')
    Tuple      = multiOp('Tuple(%s)')
    List       = multiOp('List(%s)')
    Bitor      = multiOp('Bitor(%s)')
    Bitxor     = multiOp('Bitxor(%s)')
    Bitand     = multiOp('Bitand(%s)')
    LeftShift  = mkBinOp('LeftShift')
    Power      = mkBinOp('Power')
    RightShift = mkBinOp('RightShift')
    Add        = mkBinOp('Add')
    Sub        = mkBinOp('Sub')
    Mul        = mkBinOp('Mul')
    Div        = mkBinOp('Div')
    Mod        = mkBinOp('Mod')
    FloorDiv   = mkBinOp('FloorDiv')
    Slice      = mkBinOp('Slice')
    Subscript  = mkBinOp('Getitem')


    def CallFunc(self, func, args, kw, star_node, dstar_node):
        if star_node:
            star_node=build(self,star_node)
        else:
            star_node = 'None'
        if dstar_node:
            dstar_node=build(self,dstar_node)
        else:
            dstar_node = 'None'
        return 'Call(%s,%s,%s,%s,%s)' % (
            build(self,func),self.Tuple(args),self.Dict(kw),star_node,dstar_node
        )

    def IfElse(self, trueVal, condition, falseVal):
        return 'IfElse(%s,%s,%s)' % (
            build(self, trueVal), build(self, condition), build(self, falseVal)
        )
























sb = StringBuilder()
pe = lambda s: parse_expr(s,sb)

class EventTests(TestCase):

    """Test that AST builder supports all syntax and issues correct events"""

    def testTokens(self):
        self.assertEqual(pe("a"), "a")
        self.assertEqual(pe("b"), "b")
        self.assertEqual(pe("123"), "123")
        self.assertEqual(pe("'xyz'"), "'xyz'")
        self.assertEqual(pe("'abc' 'xyz'"), "'abcxyz'")

    def testSimpleBinaries(self):
        self.assertEqual(pe("a+b"), "Add(a,b)")
        self.assertEqual(pe("b-a"), "Sub(b,a)")
        self.assertEqual(pe("c*d"), "Mul(c,d)")
        self.assertEqual(pe("c/d"), "Div(c,d)")
        self.assertEqual(pe("c%d"), "Mod(c,d)")
        self.assertEqual(pe("c//d"), "FloorDiv(c,d)")
        self.assertEqual(pe("a<<b"), "LeftShift(a,b)")
        self.assertEqual(pe("a>>b"), "RightShift(a,b)")
        self.assertEqual(pe("a**b"), "Power(a,b)")
        self.assertEqual(pe("a.b"),  "Getattr(a,'b')")
        self.assertEqual(pe("a|b"),  "Bitor(a,b)")
        self.assertEqual(pe("a&b"),  "Bitand(a,b)")
        self.assertEqual(pe("a^b"),  "Bitxor(a,b)")

    def testSimpleUnaries(self):
        self.assertEqual(pe("~a"), "Invert(a)")
        self.assertEqual(pe("+a"), "Plus(a)")
        self.assertEqual(pe("-a"), "Minus(a)")
        self.assertEqual(pe("not a"), "Not(a)")
        self.assertEqual(pe("`a`"), "repr(a)")

    if sys.version>='2.5':
        def testIfElse(self):
            self.assertEqual(pe("a if b else c"), "IfElse(a,b,c)")
            

    def testSequences(self):
        self.assertEqual(pe("a,"), "Tuple(a)")
        self.assertEqual(pe("a,b"), "Tuple(a,b)")
        self.assertEqual(pe("a,b,c"), "Tuple(a,b,c)")
        self.assertEqual(pe("a,b,c,"), "Tuple(a,b,c)")

        self.assertEqual(pe("()"), "Tuple()")
        self.assertEqual(pe("(a)"), "a")
        self.assertEqual(pe("(a,)"), "Tuple(a)")
        self.assertEqual(pe("(a,b)"), "Tuple(a,b)")
        self.assertEqual(pe("(a,b,)"), "Tuple(a,b)")
        self.assertEqual(pe("(a,b,c)"), "Tuple(a,b,c)")
        self.assertEqual(pe("(a,b,c,)"), "Tuple(a,b,c)")

        self.assertEqual(pe("[]"), "List()")
        self.assertEqual(pe("[a]"), "List(a)")
        self.assertEqual(pe("[a,]"), "List(a)")
        self.assertEqual(pe("[a,b]"), "List(a,b)")
        self.assertEqual(pe("[a,b,]"), "List(a,b)")
        self.assertEqual(pe("[a,b,c]"), "List(a,b,c)")
        self.assertEqual(pe("[a,b,c,]"), "List(a,b,c)")

        self.assertEqual(pe("{}"), "{}")
        self.assertEqual(pe("{a:b}"), "{a:b}")
        self.assertEqual(pe("{a:b,}"), "{a:b}")
        self.assertEqual(pe("{a:b,c:d}"), "{a:b,c:d}")
        self.assertEqual(pe("{a:b,c:d,1:2}"), "{a:b,c:d,1:2}")
        self.assertEqual(pe("{a:b,c:d,1:2,}"), "{a:b,c:d,1:2}")

        self.assertEqual(
            pe("{(a,b):c+d,e:[f,g]}"),
            "{Tuple(a,b):Add(c,d),e:List(f,g)}"
        )








    def testCalls(self):

        self.assertEqual(pe("a()"),    "Call(a,Tuple(),{},None,None)")
        self.assertEqual(pe("a(1,2)"), "Call(a,Tuple(1,2),{},None,None)")
        self.assertEqual(pe("a(1,2,)"), "Call(a,Tuple(1,2),{},None,None)")
        self.assertEqual(pe("a(b=3)"), "Call(a,Tuple(),{'b':3},None,None)")
        self.assertEqual(pe("a(1,2,b=3)"),
            "Call(a,Tuple(1,2),{'b':3},None,None)"
        )

        self.assertEqual(pe("a(*x)"),    "Call(a,Tuple(),{},x,None)")
        self.assertEqual(pe("a(1,*x)"),    "Call(a,Tuple(1),{},x,None)")
        self.assertEqual(pe("a(b=3,*x)"), "Call(a,Tuple(),{'b':3},x,None)")
        self.assertEqual(pe("a(1,2,b=3,*x)"),
            "Call(a,Tuple(1,2),{'b':3},x,None)"
        )

        self.assertEqual(pe("a(**y)"),    "Call(a,Tuple(),{},None,y)")
        self.assertEqual(pe("a(1,**y)"),    "Call(a,Tuple(1),{},None,y)")
        self.assertEqual(pe("a(b=3,**y)"), "Call(a,Tuple(),{'b':3},None,y)")
        self.assertEqual(pe("a(1,2,b=3,**y)"),
            "Call(a,Tuple(1,2),{'b':3},None,y)"
        )

        self.assertEqual(pe("a(*x,**y)"),    "Call(a,Tuple(),{},x,y)")
        self.assertEqual(pe("a(1,*x,**y)"),    "Call(a,Tuple(1),{},x,y)")
        self.assertEqual(pe("a(b=3,*x,**y)"), "Call(a,Tuple(),{'b':3},x,y)")
        self.assertEqual(pe("a(1,2,b=3,*x,**y)"),
            "Call(a,Tuple(1,2),{'b':3},x,y)"
        )

        self.assertRaises(SyntaxError, pe, "a(1=2)")    # expr as kw
        self.assertRaises(SyntaxError, pe, "a(b=2,c)")  # kw before positional








    def testSubscripts(self):
        self.assertEqual(pe("a[1]"),   "Getitem(a,1)")
        self.assertEqual(pe("a[2,3]"), "Getitem(a,Tuple(2,3))")
        self.assertEqual(pe("a[...]"), "Getitem(a,Ellipsis)")

        # 2-element slices (getslice)
        self.assertEqual(pe("a[:]"),   "Getitem(a,Slice(0,%s))" % MAXINT)
        self.assertEqual(pe("a[1:2]"), "Getitem(a,Slice(1,2))")
        self.assertEqual(pe("a[1:]"),  "Getitem(a,Slice(1,%s))" % MAXINT)
        self.assertEqual(pe("a[:2]"),  "Getitem(a,Slice(0,2))")

        # 3-part slice objects (getitem(slice())
        self.assertEqual(pe("a[::]"),   "Getitem(a,Sliceobj(None,None,None))")
        self.assertEqual(pe("a[1::]"),  "Getitem(a,Sliceobj(1,None,None))")
        self.assertEqual(pe("a[:2:]"),  "Getitem(a,Sliceobj(None,2,None))")
        self.assertEqual(pe("a[1:2:]"), "Getitem(a,Sliceobj(1,2,None))")
        self.assertEqual(pe("a[::3]"),  "Getitem(a,Sliceobj(None,None,3))")
        self.assertEqual(pe("a[1::3]"), "Getitem(a,Sliceobj(1,None,3))")
        self.assertEqual(pe("a[:2:3]"), "Getitem(a,Sliceobj(None,2,3))")
        self.assertEqual(pe("a[1:2:3]"),"Getitem(a,Sliceobj(1,2,3))")

    def testCompare(self):
        self.assertEqual(pe("a>b"), "Compare(a > b)")
        self.assertEqual(pe("a>=b"), "Compare(a >= b)")
        self.assertEqual(pe("a<b"), "Compare(a < b)")
        self.assertEqual(pe("a<=b"), "Compare(a <= b)")
        self.assertEqual(pe("a<>b"), "Compare(a <> b)")
        self.assertEqual(pe("a!=b"), "Compare(a != b)")
        self.assertEqual(pe("a==b"), "Compare(a == b)")
        self.assertEqual(pe("a in b"), "Compare(a in b)")
        self.assertEqual(pe("a is b"), "Compare(a is b)")
        self.assertEqual(pe("a not in b"), "Compare(a not in b)")
        self.assertEqual(pe("a is not b"), "Compare(a is not b)")
        sb.simplify_comparisons = True
        self.assertEqual(pe("1<2<3"), "And(Compare(1 < 2),Compare(2 < 3))")
        self.assertEqual(pe("a>=b>c<d"),
            "And(Compare(a >= b),Compare(b > c),Compare(c < d))")
        sb.simplify_comparisons = False
        self.assertEqual(pe("1<2<3"), "Compare(1 < 2 < 3)")
        self.assertEqual(pe("a>=b>c<d"), "Compare(a >= b > c < d)")

    def testMultiOps(self):
        self.assertEqual(pe("a and b"), "And(a,b)")
        self.assertEqual(pe("a or b"), "Or(a,b)")
        self.assertEqual(pe("a and b and c"), "And(a,b,c)")
        self.assertEqual(pe("a or b or c"), "Or(a,b,c)")
        self.assertEqual(pe("a and b and c and d"), "And(a,b,c,d)")
        self.assertEqual(pe("a or b or c or d"), "Or(a,b,c,d)")

        self.assertEqual(pe("a&b&c"), "Bitand(a,b,c)")
        self.assertEqual(pe("a|b|c"), "Bitor(a,b,c)")
        self.assertEqual(pe("a^b^c"), "Bitxor(a,b,c)")

        self.assertEqual(pe("a&b&c&d"), "Bitand(a,b,c,d)")
        self.assertEqual(pe("a|b|c|d"), "Bitor(a,b,c,d)")
        self.assertEqual(pe("a^b^c^d"), "Bitxor(a,b,c,d)")


    def testAssociativity(self):
        # Mostly this is sanity checking, since associativity and precedence
        # are primarily grammar-driven, but there are a few places where the
        # ast_builder library is responsible for correct associativity.
        self.assertEqual(pe("a+b+c"), "Add(Add(a,b),c)")
        self.assertEqual(pe("a*b*c"), "Mul(Mul(a,b),c)")
        self.assertEqual(pe("a/b/c"), "Div(Div(a,b),c)")
        self.assertEqual(pe("a//b//c"), "FloorDiv(FloorDiv(a,b),c)")
        self.assertEqual(pe("a%b%c"), "Mod(Mod(a,b),c)")
        self.assertEqual(pe("a<<b<<c"), "LeftShift(LeftShift(a,b),c)")
        self.assertEqual(pe("a>>b>>c"), "RightShift(RightShift(a,b),c)")
        self.assertEqual(pe("a.b.c"),  "Getattr(Getattr(a,'b'),'c')")
        self.assertEqual(pe("a()()"),
            "Call(Call(a,Tuple(),{},None,None),Tuple(),{},None,None)"
        )
        self.assertEqual(pe("a[b][c]"), "Getitem(Getitem(a,b),c)")
        # power is right-associative
        self.assertEqual(pe("a**b**c"), "Power(a,Power(b,c))")
        # sanity check on arithmetic precedence
        self.assertEqual(pe("5*x**2 + 4*x + -1"),
            "Add(Add(Mul(5,Power(x,2)),Mul(4,x)),Minus(1))"
        )


class ExprBuilderTests(TestCase):

    """Test that expression builder builds correct IDispatchableExpressions"""

    def setUp(self):
        self.arguments  = arguments = dict(
            [(n,Argument(name=n)) for n in 'abcdefg']
        )
        self.namespaces = namespaces = locals(),globals(),__builtins__
        self.builder    = builder    = ExprBuilder(arguments,*namespaces)

    def parse(self,expr):
        return parse_expr(expr, self.builder)

    def checkConstOrVar(self,items):
        # Verify builder's handling of global/builtin namespaces

        self.builder.bind_globals = True
        for name,val in items:
            # If bind_globals is true, return a constant for the current value
            self.assertEqual(self.builder.Name(name),Const(val),name)

    def testTokens(self):
        self.assertEqual(self.builder.Const(123), Const(123))
        for arg in self.arguments:
            self.assertEqual(self.parse(arg), Argument(name=arg))
        self.assertEqual(self.parse("123"), Const(123))
        self.assertEqual(self.parse("'xyz'"), Const('xyz'))
        self.assertEqual(self.parse("'abc' 'xyz'"), Const('abcxyz'))

    if sys.version>='2.5':
        def testIfElse(self):
            a,b,c = Argument(name='a'), Argument(name='b'), Argument(name='c')
            self.assertEqual(self.parse("a if b else c"), IfElse(a,b,c))







    def testSimpleBinariesAndUnaries(self):

        pe = self.parse
        a,b,c = Argument(name='a'), Argument(name='b'), Argument(name='c')

        self.assertEqual(pe("a+b"), Call(operator.add, a, b))
        self.assertEqual(pe("a-b"), Call(operator.sub, a, b))
        self.assertEqual(pe("b*c"), Call(operator.mul, b, c))
        self.assertEqual(pe("b/c"), Call(operator.div, b, c))
        self.assertEqual(pe("b%c"), Call(operator.mod, b, c))
        self.assertEqual(pe("b//c"), Call(operator.floordiv, b, c))
        self.assertEqual(pe("a<<b"), Call(operator.lshift, a, b))
        self.assertEqual(pe("a>>b"), Call(operator.rshift, a, b))
        self.assertEqual(pe("a**b"), Call(pow, a, b))
        self.assertEqual(pe("a.b"),  Getattr(a,'b'))
        self.assertEqual(pe("a|b"),  Call(operator.or_, a, b))
        self.assertEqual(pe("a&b"),  Call(operator.and_, a, b))
        self.assertEqual(pe("a^b"),  Call(operator.xor, a, b))

        self.assertEqual(pe("~a"), Call(operator.invert, a))
        self.assertEqual(pe("+a"), Call(operator.pos, a))
        self.assertEqual(pe("-a"), Call(operator.neg, a))
        self.assertEqual(pe("not a"), Call(operator.not_,a))
        self.assertEqual(pe("`a`"), Call(repr,a))

        self.assertEqual(pe("a and b"), AndExpr(a,b))
        self.assertEqual(pe("a or b"), OrExpr(a,b))














    def testConstantFolding(self):

        pe = self.parse

        self.assertEqual(pe("1+2"), Const(3))
        self.assertEqual(pe("2-1"), Const(1))
        self.assertEqual(pe("7*9"), Const(63))
        self.assertEqual(pe("25/10.0"), Const(2.5))
        self.assertEqual(pe("25%3"), Const(1))
        self.assertEqual(pe("25//10.0"), Const(2))
        self.assertEqual(pe("16<<4"), Const(256))
        self.assertEqual(pe("256>>4"), Const(16))
        self.assertEqual(pe("2**4"), Const(16))
        self.assertEqual(pe("dict.__class__"), Const(type))
        self.assertEqual(pe("1|5"),  Const(5))
        self.assertEqual(pe("5&1"),  Const(1))
        self.assertEqual(pe("1^2"),  Const(3))

        self.assertEqual(pe("~1"), Const(-2))
        self.assertEqual(pe("+1"), Const(1))
        self.assertEqual(pe("-1"), Const(-1))
        self.assertEqual(pe("not True"), Const(False))
        self.assertEqual(pe("`27`"), Const("27"))

        self.assertEqual(pe('1,2'), Const((1,2)))
        self.assertEqual(pe('[1,2]'), Const([1,2]))
        self.assertEqual(pe('{1:2}'), Const({1:2}))

        self.assertEqual(pe('1 and 2'), Const(2))
        self.assertEqual(pe('"" and 2'), Const(""))
        self.assertEqual(pe('"" or 53 or 27'), Const(53))

        if sys.version>="2.5":
            self.assertEqual(pe('1 if 2 else 3'), Const(1))
            self.assertEqual(pe('1 if not 2 else 3'), Const(3))






    def testSequences(self):
        pe = self.parse
        a,b,c = Argument(name='a'), Argument(name='b'), Argument(name='c')
        d,e,f = Argument(name='d'), Argument(name='e'), Argument(name='f')
        g = Argument(name='g')

        self.assertEqual(pe("a,"), Tuple(tuple,a))
        self.assertEqual(pe("a,b"), Tuple(tuple,a,b))
        self.assertEqual(pe("a,b,c"), Tuple(tuple,a,b,c))
        self.assertEqual(pe("a,b,c,"), Tuple(tuple,a,b,c))

        self.assertEqual(pe("()"), Tuple(tuple))
        self.assertEqual(pe("(a)"), a)
        self.assertEqual(pe("(a,)"), Tuple(tuple,a))
        self.assertEqual(pe("(a,b)"), Tuple(tuple,a,b))
        self.assertEqual(pe("(a,b,)"), Tuple(tuple,a,b))
        self.assertEqual(pe("(a,b,c)"), Tuple(tuple,a,b,c))
        self.assertEqual(pe("(a,b,c,)"), Tuple(tuple,a,b,c))

        self.assertEqual(pe("[]"), Tuple(list))
        self.assertEqual(pe("[a]"), Tuple(list,a))
        self.assertEqual(pe("[a,]"), Tuple(list,a))
        self.assertEqual(pe("[a,b]"), Tuple(list,a,b))
        self.assertEqual(pe("[a,b,]"), Tuple(list,a,b))
        self.assertEqual(pe("[a,b,c]"), Tuple(list,a,b,c))
        self.assertEqual(pe("[a,b,c,]"), Tuple(list,a,b,c))

        md = lambda k,v: Call(dict,Call(zip,Tuple(tuple,*k),Tuple(tuple,*v)))

        self.assertEqual(pe("{}"),md((),()))
        self.assertEqual(pe("{a:b}"),md([a],[b]))
        self.assertEqual(pe("{a:b,}"),md([a],[b]))
        self.assertEqual(pe("{a:b,c:d}"),md([a,c],[b,d]))
        self.assertEqual(pe("{a:b,c:d,1:2}"),md([a,c,Const(1)],[b,d,Const(2)]))
        self.assertEqual(pe("{a:b,c:d,1:2,}"),md([a,c,Const(1)],[b,d,Const(2)]))

        self.assertEqual(
            pe("{(a,b):c+d,e:[f,g]}"),
            md([Tuple(tuple,a,b),e], [Call(operator.add,c,d),Tuple(list,f,g)])
        )

    def testCalls(self):
        pe = self.parse

        a,b,c,d = map(self.arguments.__getitem__, "abcd")

        md = lambda k,v: Call(dict,Call(zip,Tuple(tuple,*k),Tuple(tuple,*v)))

        one_two = Const((1,2))
        b_three = Const({'b':3})
        empty = Const(())

        self.assertEqual(pe("a()"), Call(apply,a))
        self.assertEqual(pe("dict()"), Call(dict))
        self.assertEqual(pe("int(a)"), Call(int,a))

        self.assertEqual(pe("a(1,2)"), Call(apply,a,one_two))
        self.assertEqual(pe("a(1,2,)"), Call(apply,a,one_two))
        self.assertEqual(pe("a(b=3)"), Call(apply,a,empty,b_three))

        self.assertEqual(pe("a(1,2,b=3)"), Call(apply,a,one_two,b_three))

        self.assertEqual(pe("a(*b)"), Call(apply,a,b))
        self.assertEqual(pe("a(1,2,*b)"),
            Call(apply,a,Call(operator.add,one_two,Call(tuple,b))))
        self.assertEqual(pe("a(b=3,*c)"), Call(apply,a,c,b_three))

        self.assertEqual(pe("a(1,2,b=3,*c)"),
            Call(apply,a,Call(operator.add,one_two,Call(tuple,c)),b_three))

        self.assertEqual(pe("a(**c)"),  Call(apply,a,Const(()),c))
        self.assertEqual(pe("a(1,2,**c)"), Call(apply,a,one_two,c))

        self.assertEqual(pe("a(b=3,**c)"),
            Call(apply,a,Const(()),Call(predicates.add_dict, b_three, c)))

        self.assertEqual(pe("a(1,2,b=3,**c)"),
            Call(apply,a,one_two,Call(predicates.add_dict, b_three, c)))




        self.assertEqual(pe("a(b=3,*c,**d)"),
            Call(apply,a,c,Call(predicates.add_dict,b_three,d)))

        self.assertEqual(pe("a(1,2,b=3,*c,**d)"),
            Call(apply,a,Call(operator.add,one_two,Call(tuple,c)),
                Call(predicates.add_dict, b_three, d)))

        self.assertEqual(pe("a(*c,**d)"), Call(apply,a,c,d))

        self.assertEqual(pe("a(1,2,*c,**d)"),
            Call(apply,a,Call(operator.add,one_two,Call(tuple,c)),d))


    def testMultiOps(self):

        pe = self.parse
        a,b,c = Argument(name='a'), Argument(name='b'), Argument(name='c')
        d = Argument(name='d')

        self.assertEqual(pe("a and b and c"), AndExpr(a,b,c))
        self.assertEqual(pe("a or b or c"), OrExpr(a,b,c))
        self.assertEqual(pe("a and b and c and d"), AndExpr(a,b,c,d))
        self.assertEqual(pe("a or b or c or d"), OrExpr(a,b,c,d))

        self.assertEqual(pe("a&b&c"),
            Call(operator.and_,Call(operator.and_,a,b),c))

        self.assertEqual(pe("a|b|c"),
            Call(operator.or_,Call(operator.or_,a,b),c))

        self.assertEqual(pe("a^b^c"),
            Call(operator.xor,Call(operator.xor,a,b),c))









    def testSubscripts(self):
        pe = self.parse
        a,b,c = Argument(name='a'), Argument(name='b'), Argument(name='c')

        gi = lambda ob,key: Call(operator.getitem,ob,key)
        gs = lambda ob,start,stop: Call(operator.getslice,ob,start,stop)
        gso = lambda ob,*x: gi(ob, Call(slice,*map(Const,x)))

        self.assertEqual(pe("a[1]"),   gi(a,Const(1)))
        self.assertEqual(pe("a[2,3]"), gi(a,Tuple(tuple,Const(2),Const(3))))
        self.assertEqual(pe("a[...]"), gi(a,Const(Ellipsis)))

        # 2-element slices (getslice)
        self.assertEqual(pe("a[:]"),   gs(a,Const(0),Const(sys.maxint)))
        self.assertEqual(pe("a[1:2]"), gs(a,Const(1),Const(2)))
        self.assertEqual(pe("a[1:]"),  gs(a,Const(1),Const(sys.maxint)))
        self.assertEqual(pe("a[:2]"),  gs(a,Const(0),Const(2)))

        # 3-part slice objects (getitem(slice())
        self.assertEqual(pe("a[::]"),   gso(a,None,None,None))
        self.assertEqual(pe("a[1::]"),  gso(a,1,None,None))
        self.assertEqual(pe("a[:2:]"),  gso(a,None,2,None))
        self.assertEqual(pe("a[1:2:]"), gso(a,1,2,None))
        self.assertEqual(pe("a[::3]"),  gso(a,None,None,3))
        self.assertEqual(pe("a[1::3]"), gso(a,1,None,3))
        self.assertEqual(pe("a[:2:3]"), gso(a,None,2,3))
        self.assertEqual(pe("a[1:2:3]"),gso(a,1,2,3))














    def testCompare(self):
        pe = self.parse
        a,b,c = Argument(name='a'), Argument(name='b'), Argument(name='c')
        d = Argument(name='d')

        self.assertEqual(pe("a>b"), Call(operator.gt,a,b))
        self.assertEqual(pe("a>=b"), Call(operator.ge,a,b))
        self.assertEqual(pe("a<b"), Call(operator.lt,a,b))
        self.assertEqual(pe("a<=b"), Call(operator.le,a,b))
        self.assertEqual(pe("a<>b"), Call(operator.ne,a,b))
        self.assertEqual(pe("a!=b"), Call(operator.ne,a,b))
        self.assertEqual(pe("a==b"), Call(operator.eq,a,b))
        self.assertEqual(pe("a in b"), Call(predicates.in_,a,b))

        self.assertEqual(pe("a is b"), Call(predicates.is_,a,b))
        self.assertEqual(pe("a not in b"), Call(predicates.not_in,a,b))
        self.assertEqual(pe("a is not b"), Call(predicates.is_not,a,b))

        self.assertEqual(pe("1<2<3"), Const(True))
        self.assertEqual(pe("a>=b>c<d"),
            AndExpr(
                Call(operator.ge,a,b),Call(operator.gt,b,c),
                Call(operator.lt,c,d)
            )
        )

    def testTrivialMacros(self):
        a,b,c = Argument(name='a'), Argument(name='b'), Argument(name='c')
        self.arguments['q'] = Call(operator.gt,a,b)
        self.assertEqual(self.parse("q"), Call(operator.gt,a,b))
        self.assertEqual(self.parse("c and q"),
            AndExpr(c,Call(operator.gt,a,b)))









    def testSymbols(self):

        # check arguments
        for arg in self.arguments:
            self.assertEqual(self.builder.Name(arg), Argument(name=arg))

        # check locals
        self.checkConstOrVar(
            [(name,const) for name,const in self.namespaces[0].items()
                if name not in self.arguments
            ]
        )

        # check globals
        self.checkConstOrVar(
            [(name,const) for name,const in self.namespaces[1].items()
                if name not in self.arguments
                    and name not in self.namespaces[0]
            ]
        )

        # check builtins
        self.checkConstOrVar(
            [(name,const) for name,const in self.namespaces[2].items()
                if name not in self.arguments
                    and name not in self.namespaces[0]
                    and name not in self.namespaces[1]
            ]
        )

        # check non-existent
        name = 'no$such$thing'
        self.assertRaises(NameError, self.builder.Name, name)








class PredicateTests(TestCase):

    def testParseInequalities(self):

        parse = GenericFunction(lambda x,y,z:None).parse
        pe = lambda e: parse(e,locals(),globals())

        x_cmp_y = lambda n,t=True: Signature([
            (Call(getattr(operator,n),x,y),TruthCriterion(t))
        ])

        x,y = Argument(name='x'),Argument(name='y')

        for op, mirror_op, not_op, name, not_name in [
            ('>', '<', '<=','gt','le'),
            ('<', '>', '>=','lt','ge'),
            ('==','==','!=','eq','ne'),
            ('<>','<>','==','ne','eq'),
        ]:
            fwd_sig = Signature(x=Inequality(op,1))
            self.assertEqual(pe('x %s 1' % op), fwd_sig)
            self.assertEqual(pe('1 %s x' % mirror_op), fwd_sig)

            rev_sig = Signature(x=Inequality(mirror_op,1))
            self.assertEqual(pe('x %s 1' % mirror_op), rev_sig)
            self.assertEqual(pe('1 %s x' % op), rev_sig)

            not_sig = Signature(x=Inequality(not_op,1))
            self.assertEqual(pe('not x %s 1' % op), not_sig)
            self.assertEqual(pe('not x %s 1' % not_op), fwd_sig)

            self.assertEqual(pe('x %s y' % op), x_cmp_y(name))
            self.assertEqual(pe('x %s y' % not_op), x_cmp_y(not_name))

            self.assertEqual(pe('not x %s y' % op),x_cmp_y(name,False))
            self.assertEqual(pe('not x %s y' % not_op),x_cmp_y(not_name,False))





    def testParseMembership(self):
        parse = GenericFunction(lambda x,y,z:None).parse
        pe = lambda e: parse(e,locals(),globals())

        self.assertEqual(pe('x in int'), Signature(x=int))
        self.assertEqual(pe('x not in int'), Signature(x=NotCriterion(int)))
        self.assertEqual(pe('x in (1,2,3)'),
            predicates.compileIn(Argument(name='x'),[1,2,3],True))
        self.assertEqual(pe('x not in (1,2,3)'),
            predicates.compileIn(Argument(name='x'),[1,2,3],False))

        self.assertEqual(pe('x is y'),
            Signature([(Call(predicates.is_,Argument(name='x'),
                Argument(name='y')),TruthCriterion())]
            )
        )
        self.assertEqual(pe('x is not y'),
            Signature([(Call(predicates.is_not,Argument(name='x'),
                Argument(name='y')),TruthCriterion())]
            )
        )

        self.assertEqual(pe('x is TestCase'),
            Signature([(Argument(name='x'),ICriterion(Pointer(TestCase)))])
        )

        self.assertEqual(pe('x is not TestCase'),
            Signature([(Argument(name='x'),~ICriterion(Pointer(TestCase)))])
        )

        # optimization when 'is None' and type tests occur on an expression
        self.assertEqual(pe('x is None'),Signature(x=types.NoneType))
        self.assertEqual(pe('x is not None'),
            Signature(x=NotCriterion(types.NoneType)))

        self.assertEqual(pe('not (x is not None)'),Signature(x=types.NoneType))
        self.assertEqual(pe('not (x is None)'),
            Signature(x=NotCriterion(types.NoneType)))



    def testParseExpressionMatching(self):
        parse = GenericFunction(lambda x,y,z:None).parse
        pe = lambda e: parse(e,locals(),globals())

        self.assertEqual(pe('isinstance(x,int)'), Signature(x=int))

        self.assertEqual(pe('isinstance(x,(str,unicode))'),
            Signature(x=str)|Signature(x=unicode))

        self.assertEqual(pe('isinstance(x,(int,(str,unicode)))'),
            Signature(x=int)|Signature(x=str)|Signature(x=unicode))

        self.assertEqual(pe('not isinstance(x,(int,(str,unicode)))'),
            Signature(x=~ICriterion(int)&~ICriterion(str)&~ICriterion(unicode))
        )

        self.assertEqual(
            pe('issubclass(x,int)'), Signature(x=SubclassCriterion(int)))

        self.assertEqual(pe('issubclass(x,(str,unicode))'),
            Signature(x=SubclassCriterion(str)) |
            Signature(x=SubclassCriterion(unicode))
        )

        self.assertEqual(pe('issubclass(x,(int,(str,unicode)))'),
            Signature(x=SubclassCriterion(int)) |
            Signature(x=SubclassCriterion(str)) |
            Signature(x=SubclassCriterion(unicode))
        )

        self.assertEqual(pe('not issubclass(x,(int,(str,unicode)))'),
            Signature(
                x=AndCriterion(
                    *[~SubclassCriterion(x) for x in (int,str,unicode)])
                )
        )





    def testCompileIn(self):
        x = Argument(name='x')
        in_expr = predicates.compileIn(x,[1,2,3],True)
        not_in = predicates.compileIn(x,[1,2,3],False)
        self.failUnless(isinstance(not_in,Signature))
        self.failUnless(isinstance(in_expr,Predicate))
        self.assertEqual(in_expr,
            Predicate([Signature(x=Inequality('==',v)) for v in 1,2,3])
        )
        self.assertEqual(not_in,
            Signature([
                (x,reduce(operator.and_,[Inequality('<>',v) for v in 1,2,3]))
            ])
        )



























    def testParseDNF(self):

        parse = GenericFunction(lambda x,y,z:None).parse
        pe = lambda e: parse(e,locals(),globals())

        # and => Signature
        self.assertEqual(pe('x in int and y in str'),Signature(x=int,y=str))

        # or => Predicate
        self.assertEqual(pe('x in int or  y in str'),Predicate([
            Signature(x=int), Signature(y=str)
        ]))

        # Verify 'not' pushes down to the operators
        self.assertEqual(
            pe('not(x in int or y in str)'),
            Signature(x=NotCriterion(int),y=NotCriterion(str))
        )

        self.assertEqual(pe('not( x in int and y in str)'),Predicate([
            Signature(x=NotCriterion(int)), Signature(y=NotCriterion(str))
        ]))

        # ...and cancels out nested not's
        self.assertEqual(
            pe('not(x not in int or y not in str)'), Signature(x=int,y=str)
        )

        self.assertEqual(pe('not( x not in int and y not in str)'),Predicate([
            Signature(x=int), Signature(y=str)
        ]))

        # mixed and/or
        self.assertEqual(pe('x in int and y in int or z in str'),Predicate([
            Signature(x=int,y=int), Signature(z=str)
        ]))





    def testSimplePreds(self):

        [dispatch.generic()]
        def classify(age):
            """Stereotype for age"""

        def defmethod(gf,s,func):
            gf.addMethod(gf.parse(s,locals(),globals()),func)

        defmethod(classify,'not not age<2', lambda age:"infant")
        defmethod(classify,'age<13', lambda age:"preteen")
        defmethod(classify,'age<5',  lambda age:"preschooler")
        defmethod(classify,'20>age', lambda age:"teenager")
        defmethod(classify,'not age<20',lambda age:"adult")
        defmethod(classify,'age>=55',lambda age:"senior")
        defmethod(classify,'age==16',lambda age:"sweet sixteen")
        self.assertEqual(classify(25),"adult")
        self.assertEqual(classify(17),"teenager")
        self.assertEqual(classify(13),"teenager")
        self.assertEqual(classify(12.99),"preteen")
        self.assertEqual(classify(0),"infant")
        self.assertEqual(classify(4),"preschooler")
        self.assertEqual(classify(55),"senior")
        self.assertEqual(classify(54.9),"adult")
        self.assertEqual(classify(14.5),"teenager")
        self.assertEqual(classify(16),"sweet sixteen")
        self.assertEqual(classify(16.5),"teenager")
        self.assertEqual(classify(99),"senior")
        self.assertEqual(classify(Min),"infant")
        self.assertEqual(classify(Max),"senior")











TestClasses = (
    EventTests, ExprBuilderTests, PredicateTests,
)

def test_suite():
    s = []
    for t in TestClasses:
        s.append(makeSuite(t,'test'))

    return TestSuite(s)































