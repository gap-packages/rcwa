#############################################################################
##
#W  semiloc.tst                GAP4 Package `RCWA'                Stefan Kohl
##
##  This file contains automated tests of RCWA's functionality for
##  rcwa mappings of and rcwa groups over semilocalizations Z_pi of
##  the ring of integers.
##
#############################################################################

gap> START_TEST( "semiloc.tst" );
gap> RCWADoThingsToBeDoneBeforeTest();
gap> RcwaMapping(Z_pi(2),[[2,0,1]]);
Rcwa mapping of Z_( 2 ): n -> 2 n
gap> RcwaMapping(Z_pi(2),1,[[2,0,1]]);
Rcwa mapping of Z_( 2 ): n -> 2 n
gap> f := RcwaMapping([2],[[1/3,0,1]]);
Rcwa mapping of Z_( 2 ): n -> 1/3 n
gap> f * One(f) = f and One(f) * f = f;
true
gap> f * Zero(f) = Zero(f) and Zero(f) * f = Zero(f);
true
gap> IsBijective(f);
true
gap> f^2;
Rcwa permutation of Z_( 2 ): n -> 1/9 n
gap> g := f^-2;
Rcwa permutation of Z_( 2 ): n -> 9 n
gap> List([1..10],n->n^f);
[ 1/3, 2/3, 1, 4/3, 5/3, 2, 7/3, 8/3, 3, 10/3 ]
gap> Display(f);
Rcwa permutation of Z_( 2 ): n -> 1/3 n
gap> f+f;
Rcwa mapping of Z_( 2 ): n -> 2/3 n
gap> 3*f;
IdentityMapping( Z_( 2 ) )
gap> Zero(last);
ZeroMapping( Z_( 2 ), Z_( 2 ) )
gap> g := RcwaMapping([2],[[1/5,0,1]]);
Rcwa mapping of Z_( 2 ): n -> 1/5 n
gap> f + g;
Rcwa mapping of Z_( 2 ): n -> 8/15 n
gap> 7^last;
56/15
gap> IsInjective(f + g);
true
gap> IsSurjective(f + g);
false
gap> g := RcwaMapping([2],[[1/7,1/17,1]]);
Rcwa mapping of Z_( 2 ): n -> 1/7 n + 1/17
gap> IsBijective(g);
true
gap> f+g;
Rcwa mapping of Z_( 2 ): n -> 10/21 n + 1/17
gap> IsBijective(f+g);
false
gap> Print(f,"\n");
RcwaMapping( [ 2 ], [ [ 1/3, 0, 1 ] ] )
gap> String(f);
"RcwaMapping( [ 2 ], [ [ 1/3, 0, 1 ] ] )"
gap> a := RcwaMapping([2],[[3,0,2],[3,1,4],[3,0,2],[3,-1,4]]);
<rcwa mapping of Z_( 2 ) with modulus 4>
gap> Display(a);

Rcwa mapping of Z_( 2 ) with modulus 4

        /
        | 3 n / 2       if n in 0(2)
 n |-> <  (3 n + 1) / 4 if n in 1(4)
        | (3 n - 1) / 4 if n in 3(4)
        \

gap> One(a);
IdentityMapping( Z_( 2 ) )
gap> IsInjective(a);
false
gap> IsSurjective(a);
true
gap> (1/3)^a;
0
gap> (0)^a;
0
gap> a2 := a^2;
<surjective rcwa mapping of Z_( 2 ) with modulus 16>
gap> Display(a2);

Surjective rcwa mapping of Z_( 2 ) with modulus 16

        /
        | 9 n / 4        if n in 0(4)
        | (9 n - 2) / 8  if n in 2(8)
        | (9 n - 3) / 8  if n in 3(8)
        | (9 n + 3) / 8  if n in 5(8)
 n |-> <  (9 n + 2) / 8  if n in 6(8)
        | (9 n + 7) / 16 if n in 1(16)
        | (9 n + 1) / 16 if n in 7(16)
        | (9 n - 1) / 16 if n in 9(16)
        | (9 n - 7) / 16 if n in 15(16)
        \

gap> b := RcwaMapping([2,3],ShallowCopy(Coefficients(a)));
<rcwa mapping of Z_( 2, 3 ) with modulus 4>
gap> Display(b);

Rcwa mapping of Z_( 2, 3 ) with modulus 4

        /
        | 3 n / 2       if n in 0(2)
 n |-> <  (3 n + 1) / 4 if n in 1(4)
        | (3 n - 1) / 4 if n in 3(4)
        \

gap> a = b;
false
gap> IsInjective(b);
true
gap> IsSurjective(b);
true
gap> MovedPoints(b);
Z_( 2, 3 ) \ [ -1, 0, 1 ]
gap> c := b^-1;
<rcwa permutation of Z_( 2, 3 ) with modulus 3>
gap> Display(c);

Rcwa permutation of Z_( 2, 3 ) with modulus 3

        /
        | 2 n / 3       if n in 0(3)
 n |-> <  (4 n - 1) / 3 if n in 1(3)
        | (4 n + 1) / 3 if n in 2(3)
        \

gap> b*c;
IdentityMapping( Z_( 2, 3 ) )
gap> c*b;
IdentityMapping( Z_( 2, 3 ) )
gap> Order(last);
1
gap> Display(b+b);

Rcwa mapping of Z_( 2, 3 ) with modulus 4

        /
        | 3 n           if n in 0(2)
 n |-> <  (3 n + 1) / 2 if n in 1(4)
        | (3 n - 1) / 2 if n in 3(4)
        \

gap> w := RcwaMapping([2],[[1,0,2],[2,-1,1],[1,1,1],[2,-1,1]]);
<rcwa mapping of Z_( 2 ) with modulus 4>
gap> IsBijective(w);
true
gap> Display(w);

Rcwa permutation of Z_( 2 ) with modulus 4

        /
        | 2 n - 1 if n in 1(2)
 n |-> <  n / 2   if n in 0(4)
        | n + 1   if n in 2(4)
        \

gap> (w*f^-1)*((g*a)*w^-1) = w*((f^-1*g)*a)*w^-1;
true
gap> a := b;;
gap> f := RcwaMapping([2,3],[[1/5,0,1]]);
Rcwa mapping of Z_( 2, 3 ): n -> 1/5 n
gap> c := Comm(a,f);
<rcwa mapping of Z_( 2, 3 ) with modulus 3>
gap> Order(c);
2
gap> Display(c);

Rcwa permutation of Z_( 2, 3 ) with modulus 3, of order 2

        /
        | n - 1/5 if n in 1(3)
 n |-> <  n + 1/5 if n in 2(3)
        | n       if n in 0(3)
        \

gap> c = a^-1*f^-1*a*f;
true
gap> g := RcwaMapping([2,3],[[1/7,1/17,1]]);
Rcwa mapping of Z_( 2, 3 ): n -> 1/7 n + 1/17
gap> IsBijective(g);
true
gap> (f*g)*a = f*(g*a);
true
gap> a*(f^-1*g)*a^-1 = a*f^-1*(g*a^-1);
true
gap> f := RcwaMapping([2],[[1/3,1,1],[3,-3,1]]);
<rcwa mapping of Z_( 2 ) with modulus 2>
gap> Order(f);
2
gap> ClassWiseOrderPreservingOn(RcwaMapping(Z_pi(2),[[2,0,1],[0,4,1]]));
0(2)
gap> LargestSourcesOfAffineMappings(a);
[ 0(2), 1(4), 3(4) ]
gap> LargestSourcesOfAffineMappings(One(a));
[ Z_( 2, 3 ) ]
gap> Display(ClassShift(Z_pi(2)));
Tame rcwa permutation of Z_( 2 ): n -> n + 1
gap> cs := ClassShift(ResidueClass(Z_pi(2),2,0));
ClassShift( 0(2) )
gap> Display(cs);

Tame rcwa permutation of Z_( 2 ) with modulus 2, of order infinity

        /
        | n + 2 if n in 0(2)
 n |-> <  n     if n in 1(2)
        |
        \

gap> cr := ClassReflection(Z_pi(2));
ClassReflection( Z_( 2 ) )
gap> Display(cr);
Rcwa permutation of Z_( 2 ): n -> -n
gap> Order(cr);
2
gap> Display(ClassReflection(ResidueClass(Z_pi(2),2,1)));

Rcwa permutation of Z_( 2 ) with modulus 2, of order 2

        /
        | -n + 2 if n in 1(2)
 n |-> <  n      if n in 0(2)
        |
        \

gap> g := RcwaMapping(Z_pi(2),2,[[1,0,1],[3,-2,1]]);
<rcwa mapping of Z_( 2 ) with modulus 2>
gap> IsClassRotation(g); 
true
gap> cr := ClassRotation(Z_pi(2),1,2,3);
ClassRotation( 1(2), 3 )
gap> cr = g;
true
gap> IsClassRotation(ClassTransposition(0,2,1,2));
false
gap> ct := ClassTransposition(ResidueClass(Z_pi([2,3]),2,1),
>                             ResidueClass(Z_pi([2,3]),6,4));
( 1(2), 4(6) )
gap> Display(ct);

Rcwa permutation of Z_( 2, 3 ) with modulus 6, of order 2

        /
        | 3 n + 1     if n in 1(2)
 n |-> <  (n - 1) / 3 if n in 4(6)
        | n           if n in 0(6) U 2(6)
        \

gap> ct^2;
IdentityMapping( Z_( 2, 3 ) )
gap> f := RcwaMapping(Z_pi(2),[[0,2,1],[1,0,1],[3,0,2],[1,1,4]]);;
gap> Display(f:AsTable);

Rcwa mapping of Z_( 2 ) with modulus 4

                n mod 4                |             Image of n
---------------------------------------+--------------------------------------
  0                                    | 2
  1                                    | n
  2                                    | 3 n / 2
  3                                    | (n + 1) / 4

gap> IsomorphismRcwaGroup(Group(()),Z_pi(2));
[ () ] -> [ IdentityMapping( Z_( 2 ) ) ]
gap> IsomorphismRcwaGroup(TrivialGroup(IsPcGroup),Z_pi(2));
[ <identity> of ... ] -> [ IdentityMapping( Z_( 2 ) ) ]
gap> phi := IsomorphismRcwaGroup(QuaternionGroup(8),Z_pi(2));;
gap> StructureDescription(Image(phi));
"Q8"
gap> phi := IsomorphismRcwaGroup(SymmetricGroup(5),Z_pi([2,3,5]));
[ (1,2,3,4,5), (1,2) ] -> 
[ <rcwa permutation of Z_( 2, 3, 5 ) with modulus 8, of order 5>, 
  <rcwa permutation of Z_( 2, 3, 5 ) with modulus 4, of order 2> ]
gap> IsBijective(phi);
true
gap> Image(phi);
<rcwa group over Z_( 2, 3, 5 ) with 2 generators, of order 120>
gap> Size(Image(phi));
120
gap> Size(Group(GeneratorsOfGroup(Image(phi))));
120
gap> phi := IsomorphismRcwaGroup(FreeGroup(2),Z_pi(2));
[ f1, f2 ] -> [ <rcwa permutation of Z_( 2 ) with modulus 8>, 
  <rcwa permutation of Z_( 2 ) with modulus 8> ]
gap> IsBijective(phi);
true
gap> F2 := Source(phi);
<free group on the generators [ f1, f2 ]>
gap> (F2.1*F2.2^2)^phi;
<rcwa permutation of Z_( 2 ) with modulus 128>
gap> g := LocalizedRcwaMapping(ClassTransposition(2,4,3,4),2);
<rcwa mapping of Z_( 2 ) with modulus 4>
gap> h := LocalizedRcwaMapping(ClassShift(1,4),2);            
<rcwa mapping of Z_( 2 ) with modulus 4>
gap> IsConjugate(RCWA(Z_pi(2)),g,h);
false
gap> RCWADoThingsToBeDoneAfterTest();
gap> STOP_TEST( "semiloc.tst", 640000000 );

#############################################################################
##
#E  semiloc.tst . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
