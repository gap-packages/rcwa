#############################################################################
##
#W  zxz.tst                  GAP4 Package `RCWA'                  Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains automated tests of RCWA's functionality for
##  rcwa mappings of and rcwa groups over Z^2.
##
gap> START_TEST("$Id$");
gap> RCWADoThingsToBeDoneBeforeTest();
gap> L1 := [ [ 2, 1 ], [ -1, 2 ] ];;
gap> L2 := [ [ 6, 2 ], [ 0, 6 ] ];;
gap> R := DefaultRing(L1,L2);
( Integers^[ 2, 2 ] )
gap> DefaultRing([[1,2,3],[4,5,6],[7,8,9]]);
( Integers^[ 3, 3 ] )
gap> Lcm(L1,L2);
[ [ 6, 8 ], [ 0, 30 ] ]
gap> Lcm(R,L1,L2);
[ [ 6, 8 ], [ 0, 30 ] ]
gap> Lcm(L1,L1);
[ [ 1, 3 ], [ 0, 5 ] ]
gap> g := RcwaMapping( Integers^2, [[1,0],[0,6]],
>                      [[[0,0],[[[2,0],[0,1]],[0,0],2]],
>                       [[0,1],[[[4,0],[0,3]],[0,1],2]],
>                       [[0,2],[[[2,0],[0,1]],[0,0],2]],
>                       [[0,3],[[[4,0],[0,3]],[0,1],2]],
>                       [[0,4],[[[4,0],[0,1]],[2,0],2]],
>                       [[0,5],[[[4,0],[0,3]],[0,1],2]]] );
<rcwa mapping of Z^2 with modulus [ [ 1, 0 ], [ 0, 6 ] ]>
gap> Mod(g);
[ [ 1, 0 ], [ 0, 6 ] ]
gap> Mult(g);
[ [ 4, 0 ], [ 0, 3 ] ]
gap> Div(g);
2
gap> IsBalanced(g);
false
gap> Lcm(Mult(g),Mod(g));
[ [ 4, 0 ], [ 0, 6 ] ]
gap> inc := IncreasingOn(g);
(0,1)+(1,0)Z+(0,2)Z
gap> Density(inc);
1/2
gap> dec := DecreasingOn(g);
(0,0)+(1,0)Z+(0,6)Z U (0,2)+(1,0)Z+(0,6)Z
gap> Density(dec);
1/3
gap> Intersection(inc,dec);
[  ]
gap> R := Integers^2;
( Integers^2 )
gap> Source(g);
( Integers^2 )
gap> Union(inc,dec);
Z^2 \ (0,4)+(1,0)Z+(0,6)Z
gap> S := last;;
gap> Difference(R,S);
(0,4)+(1,0)Z+(0,6)Z
gap> IsClassWiseOrderPreserving(g);
true
gap> ClassWiseOrderPreservingOn(g);
( Integers^2 )
gap> ClassWiseOrderReversingOn(g);
[  ]
gap> ClassWiseConstantOn(g);
[  ]
gap> ClassWiseOrderPreservingOn(One(g));
( Integers^2 )
gap> ClassWiseConstantOn(One(g));
[  ]
gap> ClassWiseConstantOn(Zero(g));
( Integers^2 )
gap> PrimeSet(g);
[ 2, 3 ]
gap> IsOne(g);
false
gap> IsZero(g);
false
gap> l := LargestSourcesOfAffineMappings(g);
[ (0,1)+(1,0)Z+(0,2)Z, (0,0)+(1,0)Z+(0,6)Z U (0,2)+(1,0)Z+(0,6)Z, 
  (0,4)+(1,0)Z+(0,6)Z ]
gap> Union(l);
( Integers^2 )
gap> List(l,Density);
[ 1/2, 1/3, 1/6 ]
gap> ImageDensity(g);
1
gap> Multpk(g,2,1);
[  ]
gap> Multpk(g,2,0);
Z^2 \ (0,0)+(1,0)Z+(0,6)Z U (0,2)+(1,0)Z+(0,6)Z
gap> Multpk(g,2,-1);
(0,0)+(1,0)Z+(0,6)Z U (0,2)+(1,0)Z+(0,6)Z
gap> Multpk(g,3,0);
(0,0)+(1,0)Z+(0,2)Z
gap> Multpk(g,3,1);
(0,1)+(1,0)Z+(0,2)Z
gap> Union(last,last2);
( Integers^2 )
gap> Multpk(g,3,-1);
[  ]
gap> Multpk(g,3,2);
[  ]
gap> Image(g);
( Integers^2 )
gap> IsSurjective(g);
true
gap> RCWADoThingsToBeDoneAfterTest();
gap> STOP_TEST( "zxz.tst", 30000000 );

#############################################################################
##
#E  zxz.tst . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here