#############################################################################
##
#W  other.tst                 GAP4 Package `RCWA'                 Stefan Kohl
##
##  This file contains automated tests of RCWA's functionality which is not
##  directly related to rcwa groups.
##
#############################################################################

gap> START_TEST("other.tst");
gap> RCWADoThingsToBeDoneBeforeTest();
gap> IsCommuting((1,2),(3,4));
true
gap> IsCommuting((1,2,3),(3,4));
false
gap> QuotientsList([2,3,6,12,15,30]);
[ 3/2, 2, 2, 5/4, 2 ]
gap> FloatQuotientsList([2,3,6,12,15,30]);
[ 1.5, 2., 2., 1.25, 2. ]
gap> PositionsSublist([1,2,3,4,2,8,3,4,2,1,2,3,3,1,2,3],[2,3]);
[ 2, 11, 15 ]
gap> PositionsSublist([1,2,3,4,2,8,3,4,2,1,2,3,3,1,2,3],[3,3,4]);
[  ]
gap> Length(RandomCombination([1..10],5));
5
gap> IntOrInfinityToLaTeX(4);
"4"
gap> IntOrInfinityToLaTeX(infinity);
"\\infty"
gap> R := PolynomialRing(GF(4),1);; x := Z(4) * One(R);;
gap> x in DefaultRing(x);
true
gap> 2*infinity;
infinity
gap> infinity*2;
infinity
gap> infinity*infinity;
infinity
gap> DifferencesList(List([1..16],n->n^3));
[ 7, 19, 37, 61, 91, 127, 169, 217, 271, 331, 397, 469, 547, 631, 721 ]
gap> DifferencesList(last);                
[ 12, 18, 24, 30, 36, 42, 48, 54, 60, 66, 72, 78, 84, 90 ]
gap> DifferencesList(last);
[ 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6 ]
gap> QuotientsList(List([1..10],n->n^2));
[ 4, 9/4, 16/9, 25/16, 36/25, 49/36, 64/49, 81/64, 100/81 ]
gap> FloatQuotientsList(List([1..10],n->n^2));
[ 4., 2.25, 1.77778, 1.5625, 1.44, 1.36111, 1.30612, 1.26562, 1.23457 ]
gap> SearchCycle([1,4,2,3,1,2,3,1,2,3,1,2,3,1,2,3,1,2,3,1,2,3,1,2,3]);    
[ 1, 2, 3 ]
gap> SearchCycle([1,1,1,2,1,2,1,2]);
[ 1, 2 ]
gap> SearchCycle([1,1,1,2,1,2,1]);
[ 1, 2 ]
gap> SearchCycle([1,1,1,2,1,2]);
[ 1, 2 ]
gap> SearchCycle([1,1,1,2,1]);
fail
gap> SearchCycle([1,1,1,1,2,1,2]);
fail
gap> SearchCycle([1,1,1,1,2,1,2,1]);
fail
gap> SearchCycle([1,1,1,1,2,1,2,1,2]);
[ 1, 2 ]
gap> SearchCycle([1,1,1,1,2,3,1,2,3,1,2,3,1,2,3]);
[ 1, 2, 3 ]
gap> SearchCycle([1,1,1,1,6,3,1,6,3,1,6,3,1,6,3]);
[ 1, 6, 3 ]
gap> SearchCycle([1,1,1,1,6,3,1,1,6,3,1,1,6,3]);
[ 1, 1, 6, 3 ]
gap> SearchCycle([2,5,2,7,1,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7]);
[ 7 ]
gap> SearchCycle([2,5,2,7,1,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7]:alsopreperiod);
[ [ 2, 5, 2, 7, 1 ], [ 7 ] ]
gap> SearchCycle([2,5,2,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7]:alsopreperiod);
[ [ 2, 5, 2, 7 ], [ 1, 7 ] ]
gap> Trajectory(n->n^2,2,6);
[ 2, 4, 16, 256, 65536, 4294967296 ]
gap> Trajectory(n->n-1,10,[0]);
[ 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0 ]
gap> Trajectory(n->2*n,2,n->n mod 11 = 1);
[ 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024 ]
gap> NextProbablyPrimeInt(1000);
1009
gap> primes := PrimeNumbersIterator(1000);
<iterator>
gap> l := [];;
gap> for p in primes do if p > 10000 then break; fi; Add(l,p); od;
gap> Length(l);
1229
gap> l{[1..20]};
[ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71 ]
gap> primes2 := ShallowCopy(primes);
<iterator>
gap> NextIterator(primes2);
10009
gap> IsIdenticalObj(primes,primes2);
false
gap> NextIterator(primes); 
10009
gap> LaTeXStringFactorsInt(Factorial(16));
"2^{15} \\cdot 3^6 \\cdot 5^3 \\cdot 7^2 \\cdot 11 \\cdot 13"
gap> EquivalenceClasses([1..100],n->Phi(n));
[ [ 1, 2 ], [ 3, 4, 6 ], [ 5, 8, 10, 12 ], [ 7, 9, 14, 18 ], 
  [ 15, 16, 20, 24, 30 ], [ 11, 22 ], [ 13, 21, 26, 28, 36, 42 ], 
  [ 17, 32, 34, 40, 48, 60 ], [ 19, 27, 38, 54 ], [ 25, 33, 44, 50, 66 ], 
  [ 23, 46 ], [ 35, 39, 45, 52, 56, 70, 72, 78, 84, 90 ], [ 29, 58 ], 
  [ 31, 62 ], [ 51, 64, 68, 80, 96 ], [ 37, 57, 63, 74, 76 ], 
  [ 41, 55, 75, 82, 88, 100 ], [ 43, 49, 86, 98 ], [ 69, 92 ], [ 47, 94 ], 
  [ 65 ], [ 53 ], [ 81 ], [ 87 ], [ 59 ], [ 61, 77, 93, 99 ], [ 85 ], [ 67 ], 
  [ 71 ], [ 73, 91, 95 ], [ 79 ], [ 83 ], [ 89 ], [ 97 ] ]
gap> S4 := SymmetricGroup(4);; elms := AsSet(S4);;
gap> EquivalenceClasses(elms,function(g,h) return IsConjugate(S4,g,h); end);
[ [ (2,3,4), (2,4,3), (1,2,3), (1,2,4), (1,3,2), (1,3,4), (1,4,2), (1,4,3) ], 
  [ (3,4), (2,3), (2,4), (1,2), (1,3), (1,4) ], 
  [ (1,2,3,4), (1,2,4,3), (1,3,4,2), (1,3,2,4), (1,4,3,2), (1,4,2,3) ], 
  [ (1,2)(3,4), (1,3)(2,4), (1,4)(2,3) ], [ () ] ]
gap> EquivalenceClasses([3,5,2,6,8,7,12,14,15,16,6,3,6],n->Phi(n));
[ [ 2 ], [ 3, 6, 6, 3, 6 ], [ 5, 8, 12 ], [ 7, 14 ], [ 15, 16 ] ]
gap> EquivalenceClasses([(1,2),(1,2),(1,2,3)],
>                       function(g,h) return IsConjugate(S4,g,h); end);
[ [ (1,2), (1,2) ], [ (1,2,3) ] ]
gap> RestrictedPartitionsWithoutRepetitions(10,[1..10]);
[ [ 10 ], [ 9, 1 ], [ 8, 2 ], [ 7, 3 ], [ 7, 2, 1 ], [ 6, 4 ], [ 6, 3, 1 ], 
  [ 5, 4, 1 ], [ 5, 3, 2 ], [ 4, 3, 2, 1 ] ]
gap> RestrictedPartitionsWithoutRepetitions(24,DivisorsInt(24));
[ [ 24 ], [ 12, 8, 4 ], [ 12, 8, 3, 1 ], [ 12, 6, 4, 2 ], [ 12, 6, 3, 2, 1 ], 
  [ 8, 6, 4, 3, 2, 1 ] ]
gap> ListOfPowers(10,8); 
[ 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000 ]
gap> GeneratorsAndInverses(SymmetricGroup(4));
[ (1,2,3,4), (1,2), (1,4,3,2), (1,2) ]
gap> AllGraphs(1);
[ [  ] ]
gap> AllGraphs(2);
[ [  ], [ [ 1, 2 ] ] ]
gap> AllGraphs(3);
[ [  ], [ [ 1, 2 ] ], [ [ 1, 2 ], [ 1, 3 ] ], 
  [ [ 1, 2 ], [ 1, 3 ], [ 2, 3 ] ] ]
gap> AllGraphs(4);
[ [  ], [ [ 1, 2 ] ], [ [ 1, 2 ], [ 1, 3 ] ], [ [ 1, 2 ], [ 3, 4 ] ], 
  [ [ 1, 2 ], [ 1, 3 ], [ 1, 4 ] ], [ [ 1, 2 ], [ 1, 3 ], [ 2, 3 ] ], 
  [ [ 1, 2 ], [ 1, 3 ], [ 2, 4 ] ], [ [ 1, 2 ], [ 1, 3 ], [ 1, 4 ], [ 2, 3 ] ]
    , [ [ 1, 2 ], [ 1, 3 ], [ 2, 4 ], [ 3, 4 ] ], 
  [ [ 1, 2 ], [ 1, 3 ], [ 1, 4 ], [ 2, 3 ], [ 2, 4 ] ], 
  [ [ 1, 2 ], [ 1, 3 ], [ 1, 4 ], [ 2, 3 ], [ 2, 4 ], [ 3, 4 ] ] ]
gap> List(AllGraphs(5),Length);
[ 0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 
  6, 7, 7, 7, 7, 8, 8, 9, 10 ]
gap> Length(last);
34
gap> GraphClasses(1);
[ [ [  ] ] ]
gap> GraphClasses(2);
[ [ [  ] ], [ [ [ 1, 2 ] ] ] ]
gap> GraphClasses(3);
[ [ [  ] ], [ [ [ 1, 2 ] ], [ [ 2, 3 ] ], [ [ 1, 3 ] ] ], 
  [ [ [ 1, 2 ], [ 1, 3 ] ], [ [ 1, 2 ], [ 2, 3 ] ], [ [ 1, 3 ], [ 2, 3 ] ] ], 
  [ [ [ 1, 2 ], [ 1, 3 ], [ 2, 3 ] ] ] ]
gap> List(GraphClasses(4),Length);
[ 1, 6, 12, 3, 4, 4, 12, 12, 3, 6, 1 ]
gap> Sum(last);
64
gap> IdGraphNC([[6,7],[7,8],[8,9]],GraphClasses(4));
7
gap> GraphClasses(4)[7];
[ [ [ 1, 2 ], [ 1, 3 ], [ 2, 4 ] ], [ [ 1, 3 ], [ 2, 3 ], [ 2, 4 ] ], 
  [ [ 1, 2 ], [ 1, 4 ], [ 2, 3 ] ], [ [ 1, 3 ], [ 2, 4 ], [ 3, 4 ] ], 
  [ [ 1, 3 ], [ 1, 4 ], [ 2, 3 ] ], [ [ 1, 2 ], [ 2, 3 ], [ 3, 4 ] ], 
  [ [ 1, 3 ], [ 1, 4 ], [ 2, 4 ] ], [ [ 1, 4 ], [ 2, 3 ], [ 3, 4 ] ], 
  [ [ 1, 2 ], [ 2, 4 ], [ 3, 4 ] ], [ [ 1, 2 ], [ 1, 3 ], [ 3, 4 ] ], 
  [ [ 1, 4 ], [ 2, 3 ], [ 2, 4 ] ], [ [ 1, 2 ], [ 1, 4 ], [ 3, 4 ] ] ]
gap> AssignGlobals(rec(shembulli_i_pare := 1, shembulli_i_dyte := 2));
The following global variables have been assigned:
[ "shembulli_i_dyte", "shembulli_i_pare" ]
gap> shembulli_i_pare;
1
gap> G := Group(ClassTransposition(0,2,1,2),ClassShift(0,6));
<rcwa group over Z with 2 generators>
gap> AssignGeneratorVariables(G);
The following global variables have been assigned: a, b
gap> F := FreeGroup("a","b","c");;
gap> a := F.1;; b := F.2;; c := F.3;;
gap> Q := F/[a^2,b^2,c^2,(a*b)^3,(a*c)^3,(b*c)^3];
<fp group on the generators [ a, b, c ]>
gap> epis := EpimorphismsUpToAutomorphisms(Q,SymmetricGroup(4));  
[ [ a, b, c ] -> [ (3,4), (2,3), (1,3) ] ]
gap> epis := EpimorphismsUpToAutomorphisms(Q,PcGroupCode(5475,18)); # the group is SmallGroup(18,4)
[ [ a, b, c ] -> [ f1, f1*f2, f1*f3 ] ]
gap> StructureDescription(Image(epis[1]));
"(C3 x C3) : C2"
gap> if IN_LOGGING_MODE <> false then Log2HTML(IN_LOGGING_MODE); fi;
gap> RCWADoThingsToBeDoneAfterTest();
gap> STOP_TEST( "other.tst", 62000000 );

#############################################################################
##
#E  other.tst . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
