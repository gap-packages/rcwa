#############################################################################
##
#W  semiloc.tst                GAP4 Package `RCWA'                Stefan Kohl
##
#H  @(#)$Id$
##

gap> START_TEST("$Id$");
gap> f := RcwaMapping([2],[[1/3,0,1]]);
<2 - local integral rcwa mapping: n -> 1/3 n>
gap> IsBijective(f);
true
gap> f^2;
<bijective 2 - local integral rcwa mapping: n -> 1/9 n>
gap> g := f^-2;
<bijective 2 - local integral rcwa mapping: n -> 9 n>
gap> List([1..10],n->n^f);
[ 1/3, 2/3, 1, 4/3, 5/3, 2, 7/3, 8/3, 3, 10/3 ]
gap> Display(f);
Bijective 2 - local integral rcwa mapping: n -> 1/3 n
gap> f+f;
<2 - local integral rcwa mapping: n -> 2/3 n>
gap> 3*f;
<identity 2 - local integral rcwa mapping>
gap> g := RcwaMapping([2],[[1/5,0,1]]);
<2 - local integral rcwa mapping: n -> 1/5 n>
gap> f + g;
<2 - local integral rcwa mapping: n -> 8/15 n>
gap> 7^last;
56/15
gap> IsInjective(f + g);
true
gap> IsSurjective(f + g);
false
gap> g := RcwaMapping([2],[[1/7,1/17,1]]);
<2 - local integral rcwa mapping: n -> 1/7 n + 1/17>
gap> IsBijective(g);
true
gap> f+g;
<2 - local integral rcwa mapping: n -> 10/21 n + 1/17>
gap> IsBijective(f+g);
false
gap> Print(f,"\n");
SemilocalIntegralRcwaMapping( [ 2 ], [ [ 1/3, 0, 1 ] ] )
gap> String(f);
"SemilocalIntegralRcwaMapping( [ 2 ], [ [ 1/3, 0, 1 ] ] )"
gap> a := RcwaMapping([2],[[3,0,2],[3,1,4],[3,0,2],[3,-1,4]]);
<2 - local integral rcwa mapping with modulus 4>
gap> Display(a);

2 - local integral rcwa mapping with modulus 4

                n mod 4                |                 n^f
---------------------------------------+--------------------------------------
  0 2                                  | 3 n / 2
  1                                    | (3 n + 1)/4
  3                                    | (3 n - 1)/4

gap> One(a);
<identity 2 - local integral rcwa mapping>
gap> IsInjective(a);
false
gap> IsSurjective(a);
true
gap> (1/3)^a;
0
gap> (0)^a;
0
gap> a2 := a^2;
<surjective 2 - local integral rcwa mapping with modulus 16>
gap> Display(a2);

Surjective 2 - local integral rcwa mapping with modulus 16

               n mod 16                |                 n^f
---------------------------------------+--------------------------------------
   0  4  8 12                          | 9 n / 4
   1                                   | (9 n + 7)/16
   2 10                                | (9 n - 2)/8
   3 11                                | (9 n - 3)/8
   5 13                                | (9 n + 3)/8
   6 14                                | (9 n + 2)/8
   7                                   | (9 n + 1)/16
   9                                   | (9 n - 1)/16
  15                                   | (9 n - 7)/16

gap> b := SemilocalIntegralRcwaMapping([2,3],ShallowCopy(Coefficients(a)));
<2, 3 - semilocal integral rcwa mapping with modulus 4>
gap> Display(b);

2, 3 - semilocal integral rcwa mapping with modulus 4

                n mod 4                |                 n^f
---------------------------------------+--------------------------------------
  0 2                                  | 3 n / 2
  1                                    | (3 n + 1)/4
  3                                    | (3 n - 1)/4

gap> a = b;
false
gap> IsInjective(b);
true
gap> IsSurjective(b);
true
gap> c := b^-1;
<bijective 2, 3 - semilocal integral rcwa mapping with modulus 3>
gap> Display(c);

Bijective 2, 3 - semilocal integral rcwa mapping with modulus 3

                n mod 3                |                 n^f
---------------------------------------+--------------------------------------
  0                                    | 2 n / 3
  1                                    | (4 n - 1)/3
  2                                    | (4 n + 1)/3

gap> b*c;
<identity 2, 3 - semilocal integral rcwa mapping>
gap> c*b;
<identity 2, 3 - semilocal integral rcwa mapping>
gap> Order(last);
1
gap> Display(b+b);

2, 3 - semilocal integral rcwa mapping with modulus 4

                n mod 4                |                 n^f
---------------------------------------+--------------------------------------
  0 2                                  | 3 n
  1                                    | (3 n + 1)/2
  3                                    | (3 n - 1)/2

gap> w := RcwaMapping([2],[[1,0,2],[2,-1,1],[1,1,1],[2,-1,1]]);
<2 - local integral rcwa mapping with modulus 4>
gap> IsBijective(w);
true
gap> Display(w);

Bijective 2 - local integral rcwa mapping with modulus 4

                n mod 4                |                 n^f
---------------------------------------+--------------------------------------
  0                                    | n / 2
  1 3                                  | 2 n - 1
  2                                    | n + 1

gap> (w*f^-1)*((g*a)*w^-1) = w*((f^-1*g)*a)*w^-1;
true
gap> a := b;;
gap> f := RcwaMapping([2,3],[[1/5,0,1]]);
<2, 3 - semilocal integral rcwa mapping: n -> 1/5 n>
gap> c := Comm(a,f);
<2, 3 - semilocal integral rcwa mapping with modulus 3>
gap> Order(c);
2
gap> Display(c);

Bijective 2, 3 - semilocal integral rcwa mapping with modulus 3, of order 2

                n mod 3                |                 n^f
---------------------------------------+--------------------------------------
  0                                    | n
  1                                    | n - 1/5
  2                                    | n + 1/5

gap> c = a^-1*f^-1*a*f;
true
gap> g := RcwaMapping([2,3],[[1/7,1/17,1]]);
<2, 3 - semilocal integral rcwa mapping: n -> 1/7 n + 1/17>
gap> IsBijective(g);
true
gap> (f*g)*a = f*(g*a);
true
gap> a*(f^-1*g)*a^-1 = a*f^-1*(g*a^-1);
true
gap> f := RcwaMapping([2],[[1/3,1,1],[3,-3,1]]);
<2 - local integral rcwa mapping with modulus 2>
gap> Order(f);
2
gap> STOP_TEST( "semiloc.tst", 100000000 );

#############################################################################
##
#E  semiloc.tst . . . . . . . . . . . . . . . . . . . . . . . . . . ends here