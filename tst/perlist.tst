#############################################################################
##
#W  perlist.tst                GAP4 Package `RCWA'                Stefan Kohl
##
##  This file contains automated tests of RCWA's functionality for computing
##  with periodic lists. The periodic lists themselves are implemented in the
##  FR package of Laurent Bartholdi.
##
#############################################################################

gap> START_TEST( "perlist.tst" );
gap> RCWADoThingsToBeDoneBeforeTest();
gap> ct := ClassTransposition(0,3,2,3);
( 0(3), 2(3) )
gap> l := PeriodicList([],[0..11]);
[/ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 ]
gap> Permuted(l,ct);
[/ 2, 1, 0, 5, 4, 3, 8, 7, 6, 11, 10, 9 ]
gap> l := PeriodicList([17],[0..11]);
[ 17, / 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 ]
gap> Permuted(l,ct);                 
[ 1, 0, 17, / 4, 3, 2, 7, 6, 5, 10, 9, 8, 1, 0, 11 ]
gap> l := PeriodicList([17,23,45,47],[0..11]);
[ 17, 23, 45, 47, / 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 ]
gap> Permuted(l,ct);                          
[ 45, 23, 17, 1, 0, 47, / 4, 3, 2, 7, 6, 5, 10, 9, 8, 1, 0, 11 ]
gap> l := PeriodicList([17,23,45,47],[0..10]);
[ 17, 23, 45, 47, / 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ]
gap> Permuted(l,ct);                          
[ 45, 23, 17, 1, 0, 47, / 4, 3, 2, 7, 6, 5, 10, 9, 8, 2, 1, 0, 5, 4, 3, 8, 7, \
6, 0, 10, 9, 3, 2, 1, 6, 5, 4, 9, 8, 7, 1, 0, 10 ]
gap> T := RcwaMapping([[1,0,2],[3,1,2]]);;
gap> l := PeriodicList([0],[1,2]);
[ 0, / 1, 2 ]
gap> Permuted(Permuted(l,T),T) = Permuted(l,T^2);
true
gap> IsSubset([0..2],l);
true
gap> IsSubset([0..1],l);
false
gap> IsSubset(NonnegativeIntegers,l);
true
gap> IsSubset(Integers,l);           
true
gap> Sum(l);
infinity
gap> Sum(PeriodicList([],[-1,1]));                                   
fail
gap> Sum(PeriodicList([1,2],[0]));   
3
gap> Product(PeriodicList([],[-1,1]));
fail
gap> Product(PeriodicList([],[1]));   
1
gap> Product(PeriodicList([],[-1]));
fail
gap> Product(PeriodicList([],[2])); 
infinity
gap> -l;
[ 0, / -1, -2 ]
gap> l1 := PeriodicList([1,2],[0..4]);  
[ 1, 2, / 0, 1, 2, 3, 4 ]
gap> l2 := PeriodicList([1,2,3],[0..3]);
[ 1, 2, 3, / 0, 1, 2, 3 ]
gap> l1+l2;
[ 2, 4, / 3, 1, 3, 5, 7, 0, 2, 4, 6, 4, 1, 3, 5, 3, 5, 2, 4, 2, 4, 6 ]
gap> 1+l;    
[ 1, / 2, 3 ]
gap> l-1;
[ -1, / 0, 1 ]
gap> 2*l;
[ 0, / 2, 4 ]
gap> l*3;
[ 0, / 3, 6 ]
gap> (l*3)/3 = l;
true
gap> l := PeriodicList([],[1,2]);
[/ 1, 2 ]
gap> Sum(l);
infinity
gap> Product(l);
infinity
gap> l := PeriodicList([0],[1,2]);
[ 0, / 1, 2 ]
gap> Sum(l);
infinity
gap> Product(l);
0
gap> l := PeriodicList([1,2,3],[1,2,0]);
[ 1, 2, 3, / 1, 2, 0 ]
gap> Sum(l);
infinity
gap> Product(l);
0
gap> l := PeriodicList([0],[0]);
[ 0, / 0 ]
gap> Sum(l);
0
gap> Product(l);
0
gap> l := PeriodicList([-1],[1]);
[ -1, / 1 ]
gap> Sum(l);
infinity
gap> Product(l);
-1
gap> l := PeriodicList([-1],[-1]);
[ -1, / -1 ]
gap> Product(l);
fail
gap> l := PeriodicList([-1],[1,-1]);
[ -1, / 1, -1 ]
gap> Sum(l);
fail
gap> Product(l);
fail
gap> l := PeriodicList([],[1,-1,0]);
[/ 1, -1, 0 ]
gap> Sum(l);
fail
gap> Product(l);
0
gap> l := PeriodicList([-1],[1,-1,0]);
[ -1, / 1, -1, 0 ]
gap> Sum(l);
fail
gap> Product(l);
0
gap> l1 := PeriodicList([1,2,3],[1,2]);
[ 1, 2, 3, / 1, 2 ]
gap> l2 := PeriodicList([1,2,3,4],[1,2,3]);
[ 1, 2, 3, 4, / 1, 2, 3 ]
gap> -l1;
[ -1, -2, -3, / -1, -2 ]
gap> l1+l2;
[ 2, 4, 6, 5, / 3, 3, 5, 2, 4, 4 ]
gap> last-l1;
[ 1, 2, 3, 4, / 1, 2, 3 ]
gap> 2*l1;
[ 2, 4, 6, / 2, 4 ]
gap> 2*l1-l1*2;
[/ 0 ]
gap> (2*l1)/2;
[ 1, 2, 3, / 1, 2 ]
gap> l1+1;
[ 2, 3, 4, / 2, 3 ]
gap> 3+l1;
[ 4, 5, 6, / 4, 5 ]
gap> 1-l1;
[ 0, -1, -2, / 0, -1 ]
gap> T := RcwaMapping([[1,0,2],[3,1,2]]);
<rcwa mapping of Z with modulus 2>
gap> l := PeriodicList([],[1]);
[/ 1 ]
gap> Permuted(l,T);
[/ 1, 1, 2 ]
gap> Permuted(last,T);
[/ 1, 2, 2, 1, 2, 2, 1, 2, 3 ]
gap> Permuted(last,T);
[/ 1, 2, 4, 1, 3, 3, 1, 2, 4, 1, 2, 4, 1, 3, 3, 1, 2, 4, 1, 2, 4, 1, 3, 3, 1, \
2, 5 ]
gap> Sum(Period(last));
64
gap> G := WreathProduct(Group(ClassTransposition(0,2,1,2)),
>                       Group(ClassShift(0,1)));
<wild rcwa group over Z with 2 generators>
gap> IsSubgroup(CT(Integers),G);
true
gap> StructureDescription(G);
"C2 wr Z"
gap> l := PeriodicList([],[1,2]);
[/ 1, 2 ]
gap> Ball(G,l,3,Permuted:Spheres);
[ [ [/ 1, 2 ] ], [ [/ 1, 2, 1, 1 ], [/ 1, 2, 2, 2 ] ], 
  [ [/ 1, 2, 1, 1, 1, 1, 1, 1 ], [/ 1, 2, 2, 2, 2, 2, 2, 2 ] ], 
  [ [/ 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ], 
      [/ 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ] ] ]
gap> List([1..6],k->Length(Ball(G,l,k,Permuted)));
[ 3, 5, 7, 9, 11, 13 ]
gap> l := PeriodicList([],[1,2,3]);
[/ 1, 2, 3 ]
gap> List([1..6],k->Length(Ball(G,l,k,Permuted)));
[ 4, 10, 22, 44, 84, 155 ]
gap> l := PeriodicList([],[1..8]);
[/ 1, 2, 3, 4, 5, 6, 7, 8 ]
gap> List([1..6],k->Length(Ball(G,l,k,Permuted)));
[ 4, 9, 16, 24, 32, 40 ]
gap> l := PeriodicList([],[1..16]);
[/ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 ]
gap> List([1..5],k->Length(Ball(G,l,k,Permuted)));
[ 4, 10, 21, 37, 58 ]
gap> RCWADoThingsToBeDoneAfterTest();
gap> STOP_TEST( "perlist.tst", 560000000 );

#############################################################################
##
#E  perlist.tst . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
