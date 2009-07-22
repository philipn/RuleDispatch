"""Test generic functions"""

from unittest import TestCase, makeSuite, TestSuite

import operator, sys
from types import ClassType, InstanceType
from sys import maxint, version
import dispatch,protocols
from dispatch import *
from dispatch.predicates import *; from dispatch.functions import *
from protocols import Interface,advise,declareImplementation
from protocols.advice import getMRO
from dispatch import strategy, functions
from dispatch.strategy import *

class Vehicle(object):  pass
class LandVehicle(Vehicle): pass
class WaterVehicle(Vehicle): pass

class Wheeled(Interface):
    pass

class FourWheeled(Wheeled):
    pass

class TwoWheeled(Wheeled):
    pass

class GasPowered:
    pass

class HumanPowered:
    pass

class Bicycle(HumanPowered,LandVehicle): advise(instancesProvide=[TwoWheeled])
class Hummer(GasPowered,LandVehicle): advise(instancesProvide=[FourWheeled])
class Speedboat(GasPowered,WaterVehicle): pass
class PaddleBoat(HumanPowered,WaterVehicle): pass
class RiverBoat(WaterVehicle):
    advise(instancesProvide=[TwoWheeled])

class TestGraph(TestCase):

    def testItems(self):
        g = strategy.TGraph()
        self.assertEqual(g.items(),[])
        g.add(2,3)
        self.assertEqual(g.items(),[(2,3)])
        g.add(1,2)
        items = g.items(); items.sort()
        self.assertEqual(items,[(1,2),(1,3),(2,3)])

        g = strategy.TGraph()
        self.assertEqual(g.items(),[])
        g.add(1,2)
        self.assertEqual(g.items(),[(1,2)])
        g.add(2,3)
        items = g.items(); items.sort()
        self.assertEqual(items,[(1,2),(1,3),(2,3)])

        g.add(1,5); g.add(2,6)
        items = g.items(); items.sort()
        self.assertEqual(items,[(1,2),(1,3),(1,5),(1,6),(2,3),(2,6)])

    def testSuccessors(self):
        g = strategy.TGraph()
        g.add(1,2)
        self.assertEqual(g.successors([1]),{2:1})
        self.assertEqual(g.successors([2]),{})
        self.assertEqual(g.successors([3]),{})
        g.add(2,3)
        self.assertEqual(g.successors([1]),{2:1, 3:1})
        self.assertEqual(g.successors([2]),{3:1})
        self.assertEqual(g.successors([1,2]),{2:1, 3:1})
        self.assertEqual(g.successors([3]),{})
        g.add(3,1)
        self.assertEqual(g.successors([1,2,3]),{})
        items = g.items(); items.sort()
        self.assertEqual(items,
            [(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)])


class CriteriaTests(TestCase):

    def testClassCriteriaMembership(self):

        hp = ISeededCriterion(HumanPowered)

        self.failUnless(PaddleBoat in hp)
        self.failUnless(Bicycle in hp)

        self.failIf(Vehicle in hp)
        self.failIf(Speedboat in hp)
        self.failIf(Hummer in hp)
        self.failIf(object in hp)

        it = ISeededCriterion(InstanceType)
        ob = ISeededCriterion(object)

        for klass in (GasPowered,HumanPowered):
            self.failUnless(klass in it)
            self.failUnless(klass in ob)

        for klass in (Vehicle,LandVehicle,WaterVehicle,Bicycle,Hummer,
            Speedboat,PaddleBoat
        ):
            self.failIf(klass in it)
            self.failUnless(klass in ob)


    def testTestImplication(self):
        self.failUnless(ICriterion(Bicycle).implies(Wheeled))
        self.failUnless(ICriterion(PaddleBoat).implies(HumanPowered))
        self.failUnless(ICriterion(Hummer).implies(FourWheeled))
        self.failUnless(ICriterion(Hummer).implies(LandVehicle))
        self.failUnless(ICriterion(Speedboat).implies(Vehicle))
        self.failUnless(ICriterion(Wheeled).implies(object))
        self.failUnless(ICriterion(GasPowered).implies(InstanceType))
        self.failUnless(ICriterion(Wheeled).implies(Vehicle))
        self.failIf(ICriterion(object).implies(Speedboat))



    def testNullCriterion(self):
        # Null test has no seeds
        self.failIf(list(NullCriterion.seeds()))

        # and it matches anything
        self.failUnless(object in NullCriterion)
        self.failUnless(Speedboat in NullCriterion)

        # is implied by everything
        self.failUnless(ICriterion(Vehicle).implies(NullCriterion))

        # and implies nothing
        self.failIf(NullCriterion.implies(object))


    def testClassCriteriaSeedsAndDispatchFunctions(self):
        for klass in (Vehicle,LandVehicle,WaterVehicle,HumanPowered,GasPowered):
            seeds = list(ISeededCriterion(klass).seeds())
            self.failUnless(klass in seeds)
            self.failUnless(object in seeds)
            self.failIf(len(seeds)<>2)
            validateCriterion(klass,
                strategy.make_node_type(strategy.dispatch_by_mro),
                parents=[ICriterion(cls) for cls in getMRO(klass,True)])

    def testCriterionAdaptation(self):
        self.failUnless(Hummer in ISeededCriterion(Wheeled))
        self.failIf(ICriterion(Hummer).implies(Speedboat))
        self.failUnless(ICriterion(Speedboat).implies(WaterVehicle))
        self.failUnless(object in list(ISeededCriterion(InstanceType).seeds()))

    def testProtocolCriterion(self):
        self.failUnless(Bicycle in ISeededCriterion(Wheeled))
        seeds = list(ISeededCriterion(Wheeled).seeds())
        self.failUnless(Hummer in seeds)
        self.failUnless(Bicycle in seeds)
        self.failUnless(object in seeds)
        self.failUnless(len(seeds)==4)
        class BrokenBike(Bicycle): advise(instancesDoNotProvide=[Wheeled])
        self.failIf(BrokenBike in ISeededCriterion(Wheeled))

    def testSignatures(self):
        a0 = Argument(0); a1 = Argument(1)
        d1 = {a0:ICriterion(LandVehicle), a1:ICriterion(WaterVehicle)}
        d2 = {a0:ICriterion(Hummer), a1:ICriterion(Speedboat)}
        d3 = {a0:ICriterion(WaterVehicle), a1:ICriterion(LandVehicle)}
        d4 = {a0:ICriterion(LandVehicle), a1:ICriterion(LandVehicle)}

        for d in d1,d2,d3,d4:
            self.assertEqual( dict(Signature(d.items()).items()),
                dict([((k,v.node_type),v) for k,v in d.items()]) )

        s1 = Signature(d1.items())
        s2 = Signature(d2.items())
        s3 = Signature(d3.items())
        s4 = Signature(d4.items())
        s5 = PositionalSignature(
            (ICriterion(LandVehicle),ICriterion(WaterVehicle),
                ICriterion(object))
        )

        self.failUnless(s2.implies(s1)); self.failIf(s1.implies(s2))
        self.failUnless(s5.implies(s1)); self.failIf(s1.implies(s3))
        self.failIf(s1.implies(s4)); self.failIf(s2.implies(s3))
        self.failIf(s2.implies(s4)); self.failIf(s1.implies(s5))

        all_sigs = [(s1,0),(s2,0),(s3,0),(s4,0),(s5,0)]

        self.assertEqual(
            most_specific_signatures(all_sigs), [(s2,0),(s3,0),(s4,0),(s5,0)]
        )

        self.assertEqual( most_specific_signatures([(s1,0),(s2,0)]), [(s2,0)] )

        self.assertEqual( list(ordered_signatures(all_sigs)),
            [[(s2,0),(s3,0),(s4,0),(s5,0)],[(s1,0)]]
        )

        self.assertEqual( list(ordered_signatures([(s1,0),(s2,0)])),
            [[(s2,0)],[(s1,0)]]
        )

    def testMinMax(self):
        self.failUnless(Min < Max)
        self.failUnless(Max > Min)
        self.failUnless(Max == Max)
        self.failUnless(Min == Min)
        self.failIf(Min==Max or Max==Min)
        self.failUnless(Max > "xyz")
        self.failUnless(Min < "xyz")
        self.failUnless(Max > 999999)
        self.failUnless(Min < -999999)
        data = [(27,Max),(Min,99),(53,Max),(Min,27),(53,56)]
        data.sort()
        self.assertEqual(data,
            [(Min,27),(Min,99),(27,Max),(53,56),(53,Max)]
        )

        class X:
            """Ensure rich comparisons work correctly with classic classes"""

        x = X()
        for v1,v2 in [(Min,x),(x,Max)]:
            self.failUnless(v1 < v2)
            self.failUnless(v1 <= v2)
            self.failIf(v1 == v2)
            self.failUnless(v1 != v2)
            self.failUnless(v2 > v1)
            self.failUnless(v2 >= v2)

    def testIdentityDispatch(self):
        ob1, ob2, ob3 = object(),object(),object()
        id1, id2, id3 = [id(ob)&maxint for ob in [ob1,ob2,ob3]]
        table = {id1:1,id2:2,None:3}
        self.assertEqual(strategy.dispatch_by_identity(table, Vehicle), 3)
        self.assertEqual(strategy.dispatch_by_identity(table, ob1), 1)
        self.assertEqual(strategy.dispatch_by_identity(table, ob2), 2)
        self.assertEqual(strategy.dispatch_by_identity(table, ob3), 3)





    def testTruth(self):
        for t in True,False:
            validateCriterion(TruthCriterion(t),
                strategy.make_node_type(strategy.dispatch_by_truth))

    def testPointers(self):
        anOb = object()
        ptr = Pointer(anOb)
        self.assertEqual(id(anOb)&maxint,ptr)
        self.assertEqual(hash(id(anOb)&maxint),hash(ptr))
        class X: pass
        anOb = X()
        ptr = Pointer(anOb)
        oid = id(anOb)&maxint
        self.assertEqual(oid,ptr)
        self.assertEqual(hash(oid),hash(ptr))
        del anOb
        self.assertNotEqual(oid,ptr)
        self.assertEqual(ptr,ptr)
        self.assertEqual(hash(oid),hash(ptr))


    def testIdentityCriterion(self):
        ob = object()
        i = Pointer(ob)
        validateCriterion(i,
            strategy.make_node_type(strategy.dispatch_by_identity))
        i = ISeededCriterion(i)
        self.assertEqual(list(i.seeds()),[None,id(ob)&maxint])

    def testSeededIndex(self):
        i = SeededIndex(None)  # XXX
        i[SubclassCriterion(int)] = 42
        self.assertEqual(i.casemap_for([42]), {int:[42],None:[]})
        i.addSeed(int)  # make sure seed isn't duplicated
        self.assertEqual(i.casemap_for([42]), {int:[42],None:[]})
        i = SeededIndex(None)  # XXX




    def testSubclassCriterion(self):
        s = SubclassCriterion(Vehicle)
        validateCriterion(s,
            strategy.make_node_type(strategy.dispatch_by_subclass),
            parents=[SubclassCriterion(c) for c in getMRO(Vehicle,True)]
        )

        # seeds()
        self.assertEqual( s.seeds(), [Vehicle,None])

        # __contains__
        for klass in Vehicle,LandVehicle,WaterVehicle:
            self.failUnless(klass in s)
        for klass in None,GasPowered,object,Wheeled:
            self.failUnless(klass not in s)

        # implies()
        self.failUnless( s.implies(SubclassCriterion(object)) )
        self.failUnless( SubclassCriterion(LandVehicle).implies(s) )
        self.failIf( s.implies(SubclassCriterion(LandVehicle)) )
        self.failIf( SubclassCriterion(object).implies(s) )

        # eq/ne/invert
        self.assertEqual( s, SubclassCriterion(Vehicle))
        self.assertNotEqual( s, SubclassCriterion(LandVehicle))

        # matches()
        table = {LandVehicle:1,object:2,None:3}
        items = list(s.matches(table))
        self.assertEqual(items,[LandVehicle])

        # dispatch
        table = {Vehicle:1,object:2,None:3}
        self.assertEqual(strategy.dispatch_by_subclass(table, Vehicle), 1)
        self.assertEqual(strategy.dispatch_by_subclass(table, LandVehicle), 1)
        self.assertEqual(strategy.dispatch_by_subclass(table, object), 2)
        self.assertEqual(strategy.dispatch_by_subclass(table, None), 3)
        self.assertRaises(AttributeError,
            strategy.dispatch_by_subclass, table, Bicycle)


    def testInequalities(self):
        self.assertRaises(ValueError, Inequality, '', 1)
        self.assertRaises(ValueError, Inequality, 'xyz', 2)
        t1 = Inequality('>',55); t2 = Inequality('>=',100)

        self.failIf( (55,55) in t1 )
        self.failIf( (55,55) in t2 )

        self.failUnless( (100,100) in t2 )
        self.failUnless( (100,100) in t1 )
        self.failUnless( (101,101) in t2 )
        self.failUnless( (110,Max) in t2 )

        self.failUnless(t2.implies(t1))
        self.failIf(t1.implies(t2))

        t3 = Inequality('<',99)
        self.failIf(t1.implies(t3) or t2.implies(t3))
        self.failIf(t3.implies(t1) or t3.implies(t2))

        t4 = Inequality('<',"abc")
        self.failUnless(("a","a") in t4); self.failIf(("b","b") in t4)

        t5 = Inequality('==',99)

        i = strategy.InequalityIndex()
        for t in t1,t2,t3,t4,t5:
            validateCriterion(t,Inequality.node_type,seeded=False)
            i[t] = repr(t)

        ct, size = i.count_for(map(repr,[t1,t2,t3,t4,t5]))

        # Min, ..., 55, ..., 99, ..., 100, ..., 'abc', ..., Max
        self.assertEqual(ct, 11)

        # >55: 8, >=100: 5, <99: 4, <'abc': 8, ==99: 1  ---> 26
        self.assertEqual(size,26)




        # Test intersection of overlapping open intervals
        t6=Inequality('>=',6); t8=Inequality('<=',8); t68 = t6&t8
        self.assertEqual(t6.ranges, ((6,6),(6,Max)))
        self.assertEqual(t8.ranges, ((Min,8),(8,8)))
        self.assertEqual(t68.ranges, ((6,6),(6,8),(8,8)))

    def testInequalitySeeds(self):
        self.assertEqual(
            strategy.concatenate_ranges(
                {(Min,27):[], (27,27):[], (27,Max):[],
                 (Min,19):[], (19,19):[], (19,27): [],
                }
            ),
            [(Min,19),(19,27),(27,Max)],
        )
        self.assertEqual(
            strategy.concatenate_ranges(
                {(Min,19):[], (27,27):[], (19,Max):[],
                  (19,27):[], (19,19):[], (27,Max):[],
                }
            ),
            [(Min,19),(19,27),(27,Max)],
        )

    def testClasslessDispatch(self):
        class Classic: pass # Classic classes have no __class_ attribute
        strategy.dispatch_by_mro({},Classic)














    def testInequalityDispatch(self):
        classify = GenericFunction(lambda age:None)
        classify[(Inequality('<',2),)]   = lambda age:"infant"
        classify[(Inequality('<',13),)]  = lambda age:"preteen"
        classify[(Inequality('<',5),)]   = lambda age:"preschooler"
        classify[(Inequality('<',20),)]  = lambda age:"teenager"
        classify[(Inequality('>=',20),)] = lambda age:"adult"
        classify[(Inequality('>=',55),)] = lambda age:"senior"
        classify[(Inequality('=',16),)]  = lambda age:"sweet sixteen"

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


    def testTruth(self):
        self.assertEqual(TruthCriterion(27), TruthCriterion("abc"))
        self.assertNotEqual(TruthCriterion(1), TruthCriterion(False))
        self.failUnless(True in TruthCriterion(1))
        self.failUnless(False not in TruthCriterion(1))
        self.failUnless(True not in TruthCriterion(0))
        self.failUnless(False in TruthCriterion(0))
        self.failIf(TruthCriterion(1).implies(TruthCriterion(0)))
        self.failIf(TruthCriterion(0).implies(TruthCriterion(1)))
        self.failUnless(TruthCriterion(0).implies(TruthCriterion(0)))
        self.failUnless(TruthCriterion(1).implies(TruthCriterion(1)))
        self.assertEqual(TruthCriterion(42).seeds(), (True,False))
        self.assertEqual(TruthCriterion(None).seeds(), (True,False))


    def testAndOr(self):
        equals_two = Inequality('==',2)
        less_than_four = Inequality('<',4)
        lo_primes = Inequality('>',1) & less_than_four  #2, 3
        odd_primes = (~equals_two) & lo_primes
        self.failIf((4,4) in lo_primes)
        self.failUnless((3,3) in lo_primes)

        even_primes = equals_two & less_than_four

        self.failUnless((3,3) in less_than_four)
        self.failIf((4,4) in less_than_four)

        self.failIf((3,3) in even_primes)
        self.failUnless((2,2) in even_primes)

        self.failUnless(even_primes.implies(equals_two))
        self.failUnless(even_primes.implies(less_than_four))

        self.failUnless(even_primes.implies(NullCriterion))

        self.assertRaises(protocols.AdaptationFailure,
            lambda: TruthCriterion(1) & Inequality('==',1) )


















    def testRangeIntersection(self):
        ten_to_twenty = Inequality('>=',10)&Inequality('<=',20)
        fifteen_to_nineteen = (
            Inequality('>=',15) & Inequality('<=',19))

        self.failUnless( (5,5) not in ten_to_twenty )
        self.failUnless( (5,5) not in fifteen_to_nineteen )
        self.failUnless( (15,15) in ten_to_twenty )
        self.failUnless( (15,15) in fifteen_to_nineteen )
        self.failUnless( (10,10) in ten_to_twenty )
        self.failUnless( (16,17) in fifteen_to_nineteen)

        self.failUnless( fifteen_to_nineteen.implies(ten_to_twenty) )
        self.failIf(ten_to_twenty.implies(fifteen_to_nineteen))

        self.failUnless( (~ten_to_twenty).implies(~fifteen_to_nineteen) )
        self.failIf( (~fifteen_to_nineteen).implies(~ten_to_twenty) )

        for item in fifteen_to_nineteen, ten_to_twenty:
            self.failUnless( item.implies(NullCriterion) )
            self.failUnless( (~item).implies(NullCriterion) )


    def testClassIntersections(self):
        self.failUnless( Hummer in AndCriterion(LandVehicle,GasPowered) )
        self.failUnless( Speedboat in NotCriterion(LandVehicle) )
        self.failUnless( AndCriterion(LandVehicle,GasPowered).implies(
            GasPowered) )
        # This implication doesn't hold true because RiverBoat is a Wheeled
        # non-LandVehicle; if Riverboat didn't exist the implication would hold
        self.failIf( NotCriterion(LandVehicle).implies(NotCriterion(Wheeled)) )










    def testSimplifications(self):
        self.assertEqual((~TruthCriterion(1)), TruthCriterion(0))
        self.assertEqual((~(~TruthCriterion(1))), TruthCriterion(27))

        self.assertEqual(
            Inequality('>=',10) & Inequality('<=',20) & Inequality('==',15),
            Inequality('..', [(15,15)])
        )

    def testInequalityInverses(self):
        self.assertEqual(~Inequality(">=",27), Inequality("<",27))
        for op,rev in strategy.rev_ops.items():
            self.assertEqual(Inequality(op,27), ~Inequality(rev,27))



    def testTruthDispatch(self):
        x_gt_y = Call(operator.gt, Argument(name='x'), Argument(name='y'))
        greater = GenericFunction(lambda x,y:None)
        greater[Signature([(x_gt_y, TruthCriterion(False))])]= lambda x,y:False
        greater[Signature([(x_gt_y, TruthCriterion(True))])] = lambda x,y:True

        self.failIf(greater(1,10))
        self.failIf(greater(1,1))
        self.failUnless(greater(2,1))
















    def testSignatureArithmetic(self):
        x_gt_10 = Signature(x=Inequality('>',10))
        x_lt_20 = Signature(x=Inequality('<',20))
        y_in_LandVehicle = Signature(y=LandVehicle)
        empty = Signature()

        self.assertEqual((x_gt_10 & x_lt_20),
            Signature(x=Inequality('>',10) & Inequality('<',20))
        )

        self.assertEqual((x_gt_10 & y_in_LandVehicle),
            Signature(x=Inequality('>',10),y=LandVehicle)
        )

        self.assertEqual((x_gt_10 & x_gt_10), x_gt_10)
        self.assertEqual((x_gt_10 & empty), x_gt_10)
        self.assertEqual((empty & x_gt_10), x_gt_10)

        self.assertEqual((x_gt_10 | empty), empty)
        self.assertEqual((empty | x_gt_10), empty)
        self.assertEqual((x_gt_10 | x_lt_20), Predicate([x_gt_10, x_lt_20]))

        self.assertEqual((x_gt_10 | y_in_LandVehicle),
            Predicate([x_gt_10,y_in_LandVehicle])
        )

        # sig | pred
        self.assertEqual((x_gt_10 | Predicate([y_in_LandVehicle])),
            Predicate([x_gt_10,y_in_LandVehicle])
        )
        # sig & pred
        self.assertEqual((x_gt_10 & Predicate([y_in_LandVehicle])),
            Predicate([x_gt_10 & y_in_LandVehicle]))
        # pred & sig
        self.assertEqual((Predicate([y_in_LandVehicle]) & x_gt_10),
            Predicate([x_gt_10 & y_in_LandVehicle]))
        # pred | pred
        self.assertEqual((Predicate([x_gt_10]) | Predicate([y_in_LandVehicle])),
            Predicate([x_gt_10, y_in_LandVehicle])
        )

        # pred & pred
        self.assertEqual((Predicate([x_gt_10]) & Predicate([y_in_LandVehicle])),
            Predicate([x_gt_10 & y_in_LandVehicle])
        )

        # Ensure ordering preserved among conditions within a signature
        self.assertNotEqual(
            (x_gt_10 & y_in_LandVehicle).items(),
            (y_in_LandVehicle & x_gt_10).items())

        self.assertNotEqual(
            (x_gt_10 & y_in_LandVehicle & x_lt_20).items(),
            (y_in_LandVehicle & x_gt_10 & x_lt_20).items())


    def testSignatureOrdering(self):

        gt_10 = Argument(0),Inequality('>',10)
        lt_20 = Argument(1),Inequality('<',20)

        for data in [gt_10,lt_20], [lt_20,gt_10]:
            # Verify both the raw signature, and an 'and'-ed version
            for s in Signature(data), Signature(data[:1])&Signature(data[1:]):
                self.assertEqual(s.items(),
                    [((k,v.node_type),v) for k,v in data]
                )















    def testIndexEnumerables(self):
        i = SeededIndex(strategy.dispatch_by_mro)

        i[ClassCriterion(LandVehicle)] = 1
        self.assertEqual(i.casemap_for([1]),
            {LandVehicle:[1], object:[]})

        i[ClassCriterion(Bicycle)] = 2
        self.assertEqual(i.casemap_for([2]),
            {Bicycle:[2], object:[], LandVehicle:[]})

        i[ClassCriterion(HumanPowered)] = 3
        self.assertEqual(i.casemap_for([3]),
            {Bicycle:[3], object:[], LandVehicle:[], HumanPowered:[3]})

    def testIndexAnd(self):
        i = SeededIndex(strategy.dispatch_by_mro)

        i[ClassCriterion(LandVehicle) & ClassCriterion(HumanPowered)] = 1
        self.assertEqual(i.casemap_for([1]),
            {HumanPowered:[], object:[], LandVehicle:[]})

        i[ClassCriterion(Bicycle)] = 2
        self.assertEqual(i.casemap_for([1,2]),
            {HumanPowered:[], object:[], LandVehicle:[], Bicycle:[1,2]})

        i[ClassCriterion(LandVehicle)] = 3
        self.assertEqual(i.casemap_for([1,2,3]),
            {HumanPowered:[], object:[], LandVehicle:[3], Bicycle:[1,2,3]})

    def testIndexNot(self):
        i = SeededIndex(strategy.dispatch_by_mro)
        i[ClassCriterion(LandVehicle)] = 1
        i[~ClassCriterion(Bicycle)] = 2
        self.assertEqual(i.casemap_for([1,2]),
            {object:[2], LandVehicle:[1,2], Bicycle:[1]})
        i[ClassCriterion(Bicycle)] = 3
        self.assertEqual(i.casemap_for([1,2,3]),
            {object:[2], LandVehicle:[1,2], Bicycle:[1,3]})


class ExpressionTests(TestCase):

    def testArgumentBasics(self):

        self.assertRaises(ValueError, Argument)     # must specify name or posn

        self.failUnless(Argument(0) == Argument(0))
        self.failIf(    Argument(0) == Argument(1))

        self.failUnless(Argument(name="x") == Argument(name="x"))
        self.failIf(    Argument(name="x") == Argument(name="y"))

        self.failIf(    Argument(name="x") == Argument(1,"x"))
        self.failIf(    Argument(1,"x")    == Argument(name="x"))
        self.failIf(    Argument(1)        == Argument(1,"x"))
        self.failIf(    Argument(1,"x")    == Argument(1))

        self.failUnless(Argument(0,"x")    == Argument(0,"x"))
        self.failIf(    Argument(0,"x")    == Argument(0,"y"))
        self.failIf(    Argument(0,"x")    == Argument(1,"x"))
        self.failIf(    Argument(0,"x")    == Argument(1,"y"))

        a1 = Argument(0,"x"); a2 = Argument(0,"x")
        self.assertEqual(hash(a1), hash(a2))

        a1 = Argument(1); a2 = Argument(1)
        self.assertEqual(hash(a1), hash(a2))

        a1 = Argument(name="x"); a2 = Argument(name="x")
        self.assertEqual(hash(a1), hash(a2))











    def testArgumentCanonicalization(self):
        f = GenericFunction(lambda v1,v2:None)
        self.assertEqual(
            f.getExpressionId(Argument(name='v1')),
            f.getExpressionId(Argument(0))
        )
        self.assertEqual(
            f.getExpressionId(Argument(name='v2')),
            f.getExpressionId(Argument(1))
        )

    def testCalls(self):
        self.assertEqual(Call(operator.add,1,2), Call(operator.add,1,2))
        self.assertNotEqual(Call(operator.sub,1,2), Call(operator.add,1,2))
        self.assertNotEqual(Call(operator.add,2,1), Call(operator.add,1,2))

        c1 = Call(operator.add, Argument(name='x'), Argument(name='y'))
        c2 = Call(operator.add, Argument(name='x'), Argument(name='y'))
        self.assertEqual(hash(c1), hash(c2))

        c3 = Call(operator.sub, Argument(name='x'), Argument(name='y'))
        self.assertNotEqual(hash(c1), hash(c3))

        f = GenericFunction(lambda x,y:None)
        self.assertEqual(f.getExpressionId(c1), f.getExpressionId(c2))
        self.assertNotEqual(f.getExpressionId(c1), f.getExpressionId(c3))
        self.assertEqual(
            f.getExpressionId(c3),
            f.getExpressionId(
                Call(operator.sub, Argument(name='x'), Argument(name='y'))
            )
        )

        # Make the function handle 'x+y > 100'
        f[Signature([(c1,Inequality('>',100))])] = lambda x,y: "yes"
        f[Signature([])] = lambda x,y: "no"
        self.assertEqual(f(51,49), "no")
        self.assertEqual(f(99,10), "yes")
        self.assertEqual(f(27,89), "yes")


    def testConsts(self):
        f = GenericFunction(lambda x:None)
        x_plus_two = Call(operator.add,Argument(name='x'),Const(2))

        f[Signature([(x_plus_two,Inequality('>',10))])] = lambda x: True
        f[Signature([])] = lambda x: False

        self.failUnless(f(9))
        self.failIf(f(8))

        foo, bar, fourA, fourB = Const("foo"),Const("bar"),Const(4),Const(4)
        self.assertEqual(fourA,fourB)
        self.assertEqual(hash(fourA),hash(fourB))
        self.assertNotEqual(bar,foo)
        self.assertNotEqual(hash(bar),hash(foo))


    def testGetattr(self):
        vehicle_mpg = Getattr(Argument(name='v'),'mpg')
        test_mpg = lambda test,val: (vehicle_mpg,Inequality(test,val))
        fuel_efficient = GenericFunction(lambda v:None)
        fuel_efficient[Signature([test_mpg('==','N/A')])] = lambda v: True
        fuel_efficient[Signature([test_mpg('>',35)])]     = lambda v: True
        fuel_efficient[Signature([])] = lambda v: False

        b=Bicycle(); b.mpg = 'N/A'; h=Hummer();  h.mpg = 10
        self.failUnless(fuel_efficient(b))
        self.failIf(fuel_efficient(h))

        vm2 = Getattr(Argument(name='v'),'mpg')
        xm = Getattr(Argument(name='x'),'mpg')
        vg = Getattr(Argument(name='v'),'gpm')

        self.assertEqual(vehicle_mpg, vm2)
        self.assertEqual(hash(vehicle_mpg), hash(vm2))
        for item in xm,vg:
            self.assertNotEqual(vehicle_mpg, item)
            self.assertNotEqual(hash(vehicle_mpg), hash(item))



    def testTuple(self):
        xy = Tuple(tuple,Argument(name='x'),Argument(name='y'))
        xy_is_one_two = GenericFunction(lambda x,y:None)
        xy_is_one_two[Signature([(xy,Inequality('==',(1,2)))])]=lambda x,y:True
        xy_is_one_two[Signature([])] = lambda x,y: False

        self.failUnless(xy_is_one_two(1,2))
        self.failIf(xy_is_one_two(1,3))
        self.failIf(xy_is_one_two(2,1))

        xy2 = Tuple(tuple,Argument(name='x'),Argument(name='y'))
        yx = Tuple(tuple,Argument(name='y'),Argument(name='x'))
        lx = Tuple(list,Argument(name='x'),Argument(name='y'))
        zz = Tuple(tuple,Argument(name='z'),Argument(name='z'))

        self.assertEqual(xy, xy2)
        self.assertEqual(hash(xy), hash(xy2))
        for item in yx,lx,zz:
            self.assertNotEqual(xy, item)
            self.assertNotEqual(hash(xy), hash(item))

    if sys.version>='2.5':
        def testIfElse(self):
            x,y,z = Argument(name='x'), Argument(name='y'), Argument(name='z')
            xyz = IfElse(x,y,z)
            ie = GenericFunction(lambda x,y,z:None)
            ie[Signature([(xyz, TruthCriterion())])] = lambda x,y,z:True
            ie[Signature([])] = lambda x,y,z: False
            self.assertEqual(ie(1,0,0), False)
            self.assertEqual(ie(1,1,0), True)
            self.assertEqual(ie(0,1,1), False)
            self.assertEqual(ie(0,0,1), True)
            








    def testOrExpr(self):
        x, y = Argument(name='x'), Argument(name='y')
        z = Call(operator.div,Argument(name='y'),Argument(name='z'))

        xyz = OrExpr(x,y,z)
        or_ = GenericFunction(lambda x,y,z:None)
        or_[Signature([(xyz,TruthCriterion())])] = lambda x,y,z:True
        or_[Signature([])] = lambda x,y,z: False

        self.failUnless(or_(1,0,1))
        self.failIf(or_(0,0,1))
        self.assertRaises(ZeroDivisionError,or_,0,0,0)

        zyx = OrExpr(z,y,x)
        xyz2 = OrExpr(x,y,z)
        xy  = OrExpr(x,y)

        self.assertEqual(xyz, xyz2)
        self.assertEqual(hash(xyz), hash(xyz2))
        for item in xy,zyx:
            self.assertNotEqual(xyz, item)
            self.assertNotEqual(hash(xyz), hash(item))

        or_eq_23 = GenericFunction(lambda x,y:None)
        or_eq_23[Signature([(xy,Inequality('==',23))])] = lambda x,y:True
        or_eq_23[Signature([])] = lambda x,y: False
        self.failUnless(or_eq_23(23,0))
        self.failUnless(or_eq_23(0,23))
        self.failIf(or_eq_23(0,0))
        self.failIf(or_eq_23(15,15))

        or_eq_None = GenericFunction(lambda x,y:None)
        or_eq_None[Signature([(xy,Inequality('==',None))])] = lambda x,y:True
        or_eq_None[Signature([])] = lambda x,y: False
        self.failUnless(or_eq_None(None,None))
        self.failUnless(or_eq_None(0,None))
        self.failIf(or_eq_None(1,None))
        self.failIf(or_eq_None(None,1))



    def testAndExpr(self):
        x, y = Argument(name='x'), Argument(name='y')
        z = Call(operator.div,Argument(name='y'),Argument(name='z'))

        xyz = AndExpr(x,y,z)
        and_ = GenericFunction(lambda x,y,z:None)
        and_[Signature([(xyz,TruthCriterion())])] = lambda x,y,z:True
        and_[Signature([])] = lambda x,y,z: False

        self.failUnless(and_(True,True,True))
        self.failIf(and_(False,True,True))
        self.failIf(and_(False,27,0))
        self.assertRaises(ZeroDivisionError,and_,15,27,0)

        zyx = AndExpr(z,y,x)
        xyz2 = AndExpr(x,y,z)
        xy  = AndExpr(x,y)

        self.assertEqual(xyz, xyz2)
        self.assertEqual(hash(xyz), hash(xyz2))
        for item in xy,zyx:
            self.assertNotEqual(xyz, item)
            self.assertNotEqual(hash(xyz), hash(item))

        and_eq_23 = GenericFunction(lambda x,y:None)
        and_eq_23[Signature([(xy,Inequality('==',23))])] = lambda x,y:True
        and_eq_23[Signature([])] = lambda x,y: False
        self.failUnless(and_eq_23(3,23))
        self.failUnless(and_eq_23(23,23))
        self.failIf(and_eq_23(23,15))
        self.failIf(and_eq_23(23,0))

        and_eq_None = GenericFunction(lambda x,y:None)
        and_eq_None[Signature([(xy,Inequality('==',None))])] = lambda x,y:True
        and_eq_None[Signature([])] = lambda x,y: False
        self.failUnless(and_eq_None(None,None))
        self.failUnless(and_eq_None(1,None))
        self.failIf(and_eq_None(0,1))
        self.failIf(and_eq_None(1,0))


class SimpleGenerics(TestCase):

    def testTrivialities(self):
        [dispatch.on('x')]
        def f1(x,*y,**z): "foo bar"
        [dispatch.on('x')]
        def f2(x,*y,**z): "baz spam"

        for f,doc in (f1,"foo bar"),(f2,"baz spam"):
            self.assertEqual(f.__doc__, doc)

            # Empty generic should raise NoApplicableMethods
            self.assertRaises(dispatch.NoApplicableMethods, f, 1, 2, 3)
            self.assertRaises(dispatch.NoApplicableMethods, f, "x", y="z")

            # Must have at least one argument to do dispatching
            self.assertRaises(TypeError, f)
            self.assertRaises(TypeError, f, foo="bar")

    def testSimpleDefinitions(self):
        [dispatch.on('xx')]
        def g(xx,*y,**z): pass

        class Classic: pass
        class NewStyle(object): pass
        class IFoo(protocols.Interface): pass
        class Impl: protocols.advise(instancesProvide=[IFoo])
        c=Classic()
        n=NewStyle()
        i=Impl()
        for item in c,n,i,1,"blue",TestCase:
            self.assertRaises(dispatch.NoApplicableMethods, g, item)
        g.addMethod(Classic,lambda *args,**kw: ("classic!",args,kw))
        g.addMethod(NewStyle,lambda *args,**kw: ("new!",args,kw))
        g.addMethod(IFoo,lambda *args,**kw: ("foo!",args,kw))
        self.assertEqual(g(c,"foo"), ("classic!",(c,"foo",),{}))
        self.assertEqual(g(n,foo="bar"), ("new!",(n,),{'foo':'bar'}))
        self.assertEqual(g(i,"foo",x="y"), ("foo!",(i,"foo",),{"x":"y"}))
        for item in 1,"blue",TestCase:
            self.assertRaises(dispatch.NoApplicableMethods, g, item)

    def testMultiDefinition(self):
        class Classic: pass
        class NewStyle(object): pass
        class IFoo(protocols.Interface): pass
        class Impl: protocols.advise(instancesProvide=[IFoo])

        c=Classic()
        n=NewStyle()
        i=Impl()

        [dispatch.on('xx')]
        def g(xx,q=27,*y,**z): pass

        [g.when([Classic,NewStyle,IFoo])]
        def g(*args,**kw):
            return ("yes!",args,kw)

        self.assertEqual(g(c,"foo"), ("yes!",(c,"foo",),{}))
        self.assertEqual(g(n,foo="bar"), ("yes!",(n,27),{'foo':'bar'}))
        self.assertEqual(g(i,"foo",x="y"), ("yes!",(i,"foo",),{"x":"y"}))
        for item in 1,"blue",TestCase:
            self.assertRaises(dispatch.NoApplicableMethods, g, item)

    def testAdaptedDefinition(self):
        class Classic: pass
        class IFoo(protocols.Interface): pass
        class A(protocols.Adapter):
            protocols.advise(
                instancesProvide=[IFoo],asAdapterForTypes=[Classic]
            )
        [dispatch.on('xx')]
        def g(xx,*y,**z): pass

        [g.when(IFoo)]
        def g(thing, *args,**kw):
            return thing
        c=Classic(); it = g(c)
        self.assertNotEqual(it, c)
        self.failUnless(IFoo(it) is it)


    def testWhenMethods(self):

        m = GenericFunction(lambda v:None)
        m.when(Signature(v=LandVehicle))
        def foo(v):
            return "land"

        import types
        self.failUnless(isinstance(m,GenericFunction))
        self.failUnless(isinstance(foo,types.FunctionType))

        m.when(Signature(v=WaterVehicle))
        def m(v):
            return "water"

        self.failUnless(isinstance(m,types.FunctionType))
        self.assertEqual(m(LandVehicle()),"land")
        self.assertEqual(m(WaterVehicle()),"water")

        [dispatch.on('v')]
        def s(v):
            """Blah"""

        [s.when(LandVehicle)]
        def bar(v):
            return "land"

        self.failUnless(hasattr(s,'when'))
        self.failUnless(isinstance(bar,types.FunctionType))

        [s.when(WaterVehicle)]
        def s(v):
            return "water"

        self.failUnless(hasattr(s,'when'))
        self.assertEqual(s(LandVehicle()),"land")
        self.assertEqual(s(WaterVehicle()),"water")




    def testAltArg(self):
        [dispatch.on('v')]
        def s(x,v):
            """X"""

        [s.when(LandVehicle)]
        def bar(x,v):
            return "land"

        [s.when(WaterVehicle)]
        def s(x,v):
            return "water"

        self.assertEqual(s(None,LandVehicle()),"land")
        self.assertEqual(s(None,v=WaterVehicle()),"water")

    def testInstanceMethod(self):
        class X:
            [dispatch.on('v')]
            def s(x,v):
                """X"""

            [s.when(LandVehicle)]
            def bar(x,v):
                return "land"

            [s.when(WaterVehicle)]
            def s(x,v):
                return "water"

        class Y:
            s = X.s.clone()
            [s.when(WaterVehicle)]
            def s(x,v):
                return "splash!"

        self.assertEqual(X().s(v=LandVehicle()),"land")
        self.assertEqual(X().s(WaterVehicle()),"water")
        self.assertEqual(Y().s(WaterVehicle()),"splash!")


class GenericTests(TestCase):

    def testBasicSingleDispatch(self):
        m = GenericFunction(lambda v:None)
        m[(LandVehicle,)] = lambda v: "land"
        m[(WaterVehicle,)] = lambda v: "water"
        self.assertEquals(m(Hummer()), "land")
        self.assertEquals(m(Speedboat()), "water")
        self.assertRaises(NoApplicableMethods, m, GasPowered())


    def testSimpleDoubleDispatchAndNamedArgs(self):
        faster = GenericFunction(lambda v1,v2:None)
        faster[Signature(v1=GasPowered,v2=HumanPowered)] = lambda v1,v2: True
        faster[Signature(v1=Hummer,v2=Speedboat)] = lambda v1,v2: True
        faster[(object,object)] = lambda v1,v2: "dunno"
        faster[Signature(v1=HumanPowered,v2=GasPowered)] = lambda v1,v2: False
        faster[Signature(v2=Hummer,v1=Speedboat)] = lambda v1,v2: False
        self.assertEqual(faster(Hummer(),Bicycle()), True)

    def testAmbiguity(self):
        add = GenericFunction(lambda addend,augend:None)
        add[(object, int)] = operator.add
        add[(int, object)] = operator.sub
        self.assertRaises(AmbiguousMethod, add, 1, 2)

    def testDynamic(self):
        roll = GenericFunction(lambda vehicle:None)
        class Tricycle(HumanPowered,LandVehicle): pass
        roll[Signature(vehicle=Wheeled)] = lambda ob: "We're rolling"
        self.assertRaises(NoApplicableMethods, roll, Tricycle())
        declareImplementation(Tricycle,[Wheeled])
        self.assertEqual(roll(Tricycle()),"We're rolling")

    def testMRO(self):
        t = GenericFunction(lambda vehicle,num:None)
        t[Signature(vehicle=HumanPowered,num=Inequality('<',10))]=lambda v,n:False
        t[Signature(vehicle=WaterVehicle,num=Inequality('<',5))]=lambda v,n:True
        self.assertRaises(AmbiguousMethod, t, PaddleBoat(), 4)


    def testSimpleChaining(self):

        def both_vehicles(ob1,ob2):
            return "They're both vehicles."

        def both_land(next_method,ob1,ob2):
            return next_method(ob1,ob2)+"  They are both land vehicles."

        def both_sea(next_method,ob1,ob2):
            return next_method(ob1,ob2)+"  They are both sea vehicles."

        def mixed_vehicles(next_method,ob1,ob2):
            return next_method(ob1,ob2)+ \
                "  One vehicle is a land vehicle, the other is a sea vehicle."

        [dispatch.generic()]
        def compare(v1,v2): pass
        compare.addMethod([(Vehicle, Vehicle)], both_vehicles)
        compare.addMethod([(LandVehicle, LandVehicle)],both_land)
        compare.addMethod([(WaterVehicle, WaterVehicle)],both_sea)

        compare.addMethod(
            [(LandVehicle, WaterVehicle),(WaterVehicle, LandVehicle)],
            mixed_vehicles
        )

        land = Bicycle()
        sea = Speedboat()
        self.assertEqual( compare(land, land),
            "They're both vehicles.  They are both land vehicles.")

        self.assertEqual( compare(sea, sea),
            "They're both vehicles.  They are both sea vehicles.")

        self.assertEqual( compare(land, sea), "They're both vehicles.  \
One vehicle is a land vehicle, the other is a sea vehicle.")

        self.assertEqual( compare(sea, land), "They're both vehicles.  \
One vehicle is a land vehicle, the other is a sea vehicle.")


    def testSubexpressionOrderingConstraints(self):

        g = GenericFunction(lambda x,y:None)
        self.assertEqual(g.constraints.items(),[])

        df = Inequality.node_type
        yx = Call(operator.div, Argument(name='y'), Argument(name='x'))
        yxid = g.getExpressionId(yx), df
        xid = g.getExpressionId(Argument(name='x')), df
        yid = g.getExpressionId(Argument(name='y')), df

        [g.when('x==2 and y>10 and x<27')]
        def x(x,y):
            return "foo"

        self.assertEqual(g.constraints.items(),[])

        [g.when('x>0 and y/x>10')]
        def x(x,y):
            return "bar"

        self.assertEqual(g.constraints.items(),[(xid,yxid)])

        [g.when('x==1 and y>0 and y/x>10')]
        def x(x,y):
            return "bar"

        items = g.constraints.items(); items.sort()
        expected = [(xid,yxid),(yid,yxid)]; expected.sort()
        self.assertEqual(items,expected)
        self.assertEqual(g.constraints.successors([yid,yxid]),{yxid:1})
        self.assertEqual(g.constraints.successors([xid,yxid]),{yxid:1})

        best_id, remaining_ids = g._best_split(range(len(g.cases)), [yxid,yid])
        self.assertEqual(best_id, yid)

        best_id, remaining_ids = g._best_split(range(len(g.cases)), [yxid,xid])
        self.assertEqual(best_id, xid)



    def testSimpleMultiDispatch(self):
        class A: pass
        class B(A): pass
        class C: pass
        class D(A,C): pass

        def m1(*x): return "m1"
        def m2(*x): return "m2"
        def m3(*x): return "m3"
        def m4(*x): return "m4"
        def m5(*x): return "m5"

        class T: pass
        class F: pass

        tf = [F(),T()]

        g = GenericFunction(
            lambda f1,f1_x,f2,f1x_at_not_B, f1_y_eq_f2_y: None)

        # f1, f1.x, f2, f1.x@!B, f1.y=f2.y

        g.addMethod([(A,A,NullCriterion,T,T)], m1)
        g.addMethod([(B,B),(C,B,A)], m2)
        g.addMethod([(C,NullCriterion,C)], m3)
        g.addMethod([(C,)], m4)
        g.addMethod([(T,)], m5)

        def w(f1,f1x,f2,ymatches=F()):
            return g(f1,f1x,f2,tf[not isinstance(f1x,B)],ymatches)

        for time in 1,2:
            self.assertEqual( w(A(),A(),C(),T()), "m1")
            self.assertEqual( w(B(),B(),C()),     "m2")
            self.assertEqual( w(C(),B(),B()),     "m2")
            self.assertEqual( w(C(),C(),C()),     "m3")
            self.assertEqual( w(C(),A(),A()),     "m4")
            self.assertEqual( g(T(),None,None,None,None), "m5")
            g.criterionChanged()


    def testInstanceMethods(self):
        class X:
            [dispatch.generic()]
            def s(self,v):
                """X"""

            [s.when("v in LandVehicle")]
            def bar(self,v):
                return "land"

            [s.when("v in WaterVehicle")]
            def s(self,v):
                return "water"

        class Y(X):
            s = X.s

            [s.when("v in WaterVehicle")]
            def s(self,v):
                return "splash!"

        self.assertEqual(Y().s(WaterVehicle()),"splash!")
        self.assertEqual(X().s(v=LandVehicle()),"land")
        self.assertEqual(X().s(WaterVehicle()),"water")


    def testSubclassDispatch(self):
        [dispatch.generic()]
        def gm (t) : pass

        [gm.when(default)]
        def gm (t) : return 'default'

        [gm.when('issubclass(t,int)')]
        def gm2 (t) : return 'int'

        self.assertEqual(gm(int),"int")
        self.assertEqual(gm(object),"default")
        self.assertEqual(gm(float),"default")


    def testArgNormalization(self):
        from dispatch.functions import _mkNormalizer
        class dispatcher:
            def __getitem__(self,argtuple):
                return lambda *_,**__: argtuple

        f,a = _mkNormalizer(lambda foo: None, dispatcher())
        self.assertEqual(a,['foo'])
        self.assertEqual(f("bar"), ("bar",))
        self.assertEqual(f(foo="bar"), ("bar",))

        f,a = _mkNormalizer(lambda foo=42: None, dispatcher())
        self.assertEqual(a,['foo'])
        self.assertEqual(f("bar"), ("bar",))
        self.assertEqual(f(foo="bar"), ("bar",))
        self.assertEqual(f(), (42,))

        f,a = _mkNormalizer(lambda foo,*z: None, dispatcher())
        self.assertEqual(a,['foo','z'])
        self.assertEqual(f("bar","baz"), ("bar",("baz",)))
        self.assertEqual(f(foo="bar"), ("bar",()))

        f,a = _mkNormalizer(lambda foo="shoo",blue=42,*z: None, dispatcher())
        self.assertEqual(a,['foo','blue','z'])
        self.assertEqual(f("bar","baz"), ("bar","baz",()))
        self.assertEqual(f("bar","baz","spam"), ("bar","baz",("spam",)))
        self.assertEqual(f(foo="bar"), ("bar",42,()))
        self.assertEqual(f(blue="two"), ("shoo","two",()))
        self.assertEqual(f(1,2,3,4), (1,2,(3,4)))
        self.assertEqual(f(), ("shoo",42,()))

        f,a = _mkNormalizer(lambda (x,y): None, dispatcher())
        self.assertEqual(a,['x','y'])
        self.assertEqual(f((1,2)), (1,2))

        f,a = _mkNormalizer(lambda foo,(x,y),*z,**zz: None, dispatcher())
        self.assertEqual(a,['foo','x','y','z','zz'])
        self.assertEqual(
            f("foo",(1,2),fizz="fuzz"), ("foo",1,2,(),{'fizz':'fuzz'})
        )

    def testKwArgHandling(self):
        [dispatch.generic()]
        def f(**fiz): """Test of kw handling"""

        [f.when("'x' in fiz")]
        def f(**fiz): return "x"

        [f.when("'y' in fiz")]
        def f(**fiz): return "y"

        self.assertEqual(f(x=1),"x")
        self.assertEqual(f(y=1),"y")
        self.assertRaises(AmbiguousMethod, f, x=1, y=1)

    def testVarArgHandling(self):
        [dispatch.generic()]
        def f(*fiz): """Test of vararg handling"""

        [f.when("'x' in fiz")]
        def f(*fiz): return "x"

        [f.when("'y' in fiz")]
        def f(*fiz): return "y"

        self.assertEqual(f("foo","x"),"x")
        self.assertEqual(f("bar","q","y"),"y")
        self.assertEqual(f("bar","q","y"),"y")
        self.assertEqual(f("y","q",),"y")
        self.assertRaises(AmbiguousMethod, f, "x","y")

    def test_NoApplicableMethods_is_raised(self):
        [dispatch.generic()]
        def demo_func(number):
            pass
        demo_func.when("number < 10")(lambda x: 0)
        self.assertEqual(demo_func(3),0)
        self.assertRaises(dispatch.NoApplicableMethods, demo_func, 33)




TestClasses = (
    TestGraph, CriteriaTests, ExpressionTests, SimpleGenerics, GenericTests,
)

def test_combiners():
    import doctest 
    return doctest.DocFileSuite(
        'combiners.txt', optionflags=doctest.ELLIPSIS, package='dispatch',
    )

def test_suite():
    return TestSuite(
        [test_combiners()] +
        [makeSuite(t,'test') for t in TestClasses]
    )


























