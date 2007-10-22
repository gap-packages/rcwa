#############################################################################
##
#W  cscrct.tst                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains automated tests related to series of rcwa permutations
##  like class shifts, -reflections, -rotations and -transpositions.
##
gap> START_TEST("$Id$");
gap> RCWADoThingsToBeDoneBeforeTest();
gap> x := Indeterminate(GF(4),1);; SetName(x,"x");
gap> R1 := PolynomialRing(GF(4),1);
GF(2^2)[x]
gap> y := Indeterminate(GF(25),1);; SetName(y,"y");
gap> R2 := PolynomialRing(GF(25),1);
GF(5^2)[y]
gap> ClassShift(Integers,1,2);
ClassShift(1,2)
gap> ClassShift([Integers,1,2]);
ClassShift(1,2)
gap> last^2;
ClassShift(1,2)^2
gap> LaTeXName(last);
"\\nu_{1(2)}^{2}"
gap> last2^3;
ClassShift(1,2)^6
gap> LaTeXName(last);
"\\nu_{1(2)}^{6}"
gap> last2^-1;
ClassShift(1,2)^-6
gap> LaTeXName(last);
"\\nu_{1(2)}^{-6}"
gap> last2^-2;
ClassShift(1,2)^12
gap> LaTeXName(last);
"\\nu_{1(2)}^{12}"
gap> ClassShift(Z_pi(2),0,4);
ClassShift(0,4)
gap> ClassShift(0,3);
ClassShift(0,3)
gap> ClassShift(R1,Zero(R1),x);
ClassShift(0*Z(2),x)
gap> Source(last);
GF(2^2)[x]
gap> ClassShift(Zero(R1),x);
ClassShift(0*Z(2),x)
gap> Display(last);

Bijective rcwa mapping of GF(2)[x] with modulus x, of order 2

         P mod x          |              P^ClassShift(0*Z(2),x)
--------------------------+---------------------------------------------------
 0*Z(2)                   | P + x
 Z(2)^0                   | P

gap> ClassShift([Zero(R1),x]);
ClassShift(0*Z(2),x)
gap> Source(last);
GF(2)[x]
gap> ClassShift(Integers,ResidueClass(2,3));
ClassShift(2,3)
gap> ClassShift(ResidueClass(2,3));
ClassShift(2,3)
gap> ClassShift(R1,ResidueClass(R1,x,Zero(x)));
ClassShift(0*Z(2),x)
gap> Display(last);

Bijective rcwa mapping of GF(2^2)[x] with modulus x, of order 2

         P mod x          |              P^ClassShift(0*Z(2),x)
--------------------------+---------------------------------------------------
 0*Z(2)                   | P + x
 Z(2)^0   Z(2^2)          |
 Z(2^2)^2                 | P

gap> ClassShift(ResidueClass(R1,x,Zero(x)));
ClassShift(0*Z(2),x)
gap> Source(last);
GF(2^2)[x]
gap> ClassShift(Integers);
ClassShift(0,1)
gap> ClassShift(Z_pi([2,3]));
ClassShift(0,1)
gap> ClassShift([Z_pi([2,3])]);
ClassShift(0,1)
gap> ClassShift(R1);
ClassShift(0*Z(2),Z(2)^0)
gap> Display(last);
Bijective rcwa mapping of GF(2^2)[x]: P -> P + Z(2)^0
gap> ClassReflection(Integers,1,2);
ClassReflection(1,2)
gap> ClassReflection([Integers,1,2]);
ClassReflection(1,2)
gap> ClassReflection(Z_pi(2),0,4);
ClassReflection(0,4)
gap> ClassReflection(0,3);
ClassReflection(0,3)
gap> ClassReflection(R1,Zero(R1),x);
IdentityMapping( GF(2^2)[x] )
gap> IsRcwaMapping(last);
true
gap> ClassReflection(R2,Zero(R2),y);
ClassReflection(0*Z(5),y)
gap> last^2;
IdentityMapping( GF(5^2)[y] )
gap> ClassReflection(Zero(R2),y);
ClassReflection(0*Z(5),y)
gap> ClassReflection([Zero(R2),y]);
ClassReflection(0*Z(5),y)
gap> Source(last);
GF(5)[y]
gap> ClassReflection(Integers,ResidueClass(2,3));
ClassReflection(2,3)
gap> ClassReflection(ResidueClass(2,3));
ClassReflection(2,3)
gap> ClassReflection(R2,ResidueClass(R2,y,Zero(y)));
ClassReflection(0*Z(5),y)
gap> Source(last);
GF(5^2)[y]
gap> ClassReflection(ResidueClass(R2,y,Zero(y)));
ClassReflection(0*Z(5),y)
gap> Source(last);
GF(5^2)[y]
gap> ClassReflection(Integers);
ClassReflection(0,1)
gap> ClassReflection(Z_pi([2,3]));
ClassReflection(0,1)
gap> ClassReflection([Z_pi([2,3])]);
ClassReflection(0,1)
gap> Display(last);
Bijective rcwa mapping of Z_( 2, 3 ): n -> -n
gap> ClassReflection(R2);
ClassReflection(0*Z(5),Z(5)^0)
gap> Display(last);
Bijective rcwa mapping of GF(5^2)[y]: P -> -P
gap> ClassRotation(Integers,-1);
ClassReflection(0,1)
gap> ClassRotation(Integers,1);
IdentityMapping( Integers )
gap> ClassRotation(Z_pi(2),-1);
ClassReflection(0,1)
gap> ClassRotation(Z_pi(2),1);
IdentityMapping( Z_( 2 ) )
gap> ClassRotation(Z_pi(2),1/3);
ClassRotation(0,1,1/3)
gap> ClassRotation(Z_pi(2),-1/3);
ClassRotation(0,1,-1/3)
gap> ClassRotation(Z_pi(2),1/3);
ClassRotation(0,1,1/3)
gap> Display(last);
Tame bijective rcwa mapping of Z_( 2 ): n -> 1/3 n
gap> ClassRotation(Z_pi(2),ResidueClass(Z_pi(2),2,1),3/5);
ClassRotation(1,2,3/5)
gap> Display(last);

Tame bijective rcwa mapping of Z_( 2 ) with modulus 2, of order infinity

                n mod 2                |       n^ClassRotation(1,2,3/5)
---------------------------------------+--------------------------------------
  0                                    | n
  1                                    | 3/5 n + 2/5

gap> ClassRotation(ResidueClass(Z_pi(2),2,1),3/5);
ClassRotation(1,2,3/5)
gap> ClassRotation([ResidueClass(Z_pi(2),2,1),3/5]);
ClassRotation(1,2,3/5)
gap> ClassRotation(R1,ResidueClass(R1,x,Zero(R1)),Z(4)*One(R1));
ClassRotation(0*Z(2),x,Z(2^2))
gap> Display(last);

Bijective rcwa mapping of GF(2^2)[x] with modulus x, of order 3

         P mod x          |        P^(ClassRotation(0*Z(2),x,Z(2^2)))
--------------------------+---------------------------------------------------
 0*Z(2)                   | Z(2^2)*P
 Z(2)^0   Z(2^2)          |
 Z(2^2)^2                 | P

gap> last^-1;
ClassRotation(0*Z(2),x,Z(2^2))^2
gap> ClassRotation(R1,Z(4)*One(R1));
ClassRotation(0*Z(2),Z(2)^0,Z(2^2))
gap> Display(last);
Bijective rcwa mapping of GF(2^2)[x]: P -> Z(2^2)*P
gap> last^2;
ClassRotation(0*Z(2),Z(2)^0,Z(2^2))^2
gap> Display(last);
Bijective rcwa mapping of GF(2^2)[x]: P -> Z(2^2)^2*P
gap> ClassRotation(R2,ResidueClass(R2,y^2,y+1),Z(25)*One(R2));
ClassRotation(y+Z(5)^0,y^2,Z(5^2))
gap> last^2;
ClassRotation(y+Z(5)^0,y^2,Z(5^2))^2
gap> last^5;
ClassRotation(y+Z(5)^0,y^2,Z(5^2))^10
gap> last^12;
IdentityMapping( GF(5^2)[y] )
gap> ClassTransposition(0,2,1,2);
ClassTransposition(0,2,1,2)
gap> ClassTransposition(Integers,0,2,1,2);
ClassTransposition(0,2,1,2)
gap> ClassTransposition(Z_pi(2),0,2,1,2);
ClassTransposition(0,2,1,2)
gap> Display(last);

Bijective rcwa mapping of Z_( 2 ) with modulus 2, of order 2

                n mod 2                |    n^ClassTransposition(0,2,1,2)
---------------------------------------+--------------------------------------
  0                                    | n + 1
  1                                    | n - 1

gap> LaTeXName(last);
"\\tau_{0(2),1(2)}"
gap> ClassTransposition(Z_pi(2),0,2,1,4);
ClassTransposition(0,2,1,4)
gap> Support(last);
Z_( 2 ) \ 3(4)
gap> ClassTransposition(ResidueClass(0,3),ResidueClass(1,3));
ClassTransposition(0,3,1,3)
gap> Support(last);
Z \ 2(3)
gap> ClassTransposition(Integers,ResidueClass(0,3),ResidueClass(1,3));
ClassTransposition(0,3,1,3)
gap> ClassTransposition(ResidueClass(Z_pi([2,3]),3,0),
>                       ResidueClass(Z_pi([2,3]),3,1));
ClassTransposition(0,3,1,3)
gap> Support(last);
Z_( 2, 3 ) \ 2(3)
gap> Display(last2);

Bijective rcwa mapping of Z_( 2, 3 ) with modulus 3, of order 2

                n mod 3                |    n^ClassTransposition(0,3,1,3)
---------------------------------------+--------------------------------------
  0                                    | n + 1
  1                                    | n - 1
  2                                    | n

gap> ClassTransposition(Z_pi([2,3]),
>                       ResidueClass(Z_pi([2,3]),3,0),
>                       ResidueClass(Z_pi([2,3]),3,1));
ClassTransposition(0,3,1,3)
gap> TransposedClasses(last);
[ 0(3), 1(3) ]
gap> IsClassTransposition(last2);
true
gap> ClassTransposition(R1,ResidueClass(R1,x,Zero(R1)),
>                          ResidueClass(R1,x^2,x+1));
ClassTransposition(0*Z(2),x,x+Z(2)^0,x^2)
gap> TransposedClasses(last);
[ 0*Z(2)(mod x), x+Z(2)^0(mod x^2) ]
gap> Support(last2);
0*Z(2)(mod x) U x+Z(2)^0(mod x^2)
gap> Source(last3);
GF(2^2)[x]
gap> ClassTransposition(ResidueClass(R1,x,Zero(R1)),
>                       ResidueClass(R1,x^2,x+1));
ClassTransposition(0*Z(2),x,x+Z(2)^0,x^2)
gap> Display(last);

Bijective rcwa mapping of GF(2^2)[x] with modulus x^2, of order 2

        P mod x^2         |   P^(ClassTransposition(0*Z(2),x,x+Z(2)^0,x^2))
--------------------------+---------------------------------------------------
 0*Z(2)                   |
 x                        |
 Z(2^2)*x                 |
 Z(2^2)^2*x               | x*P + x+Z(2)^0
 Z(2)^0                   |
 Z(2^2)                   |
 Z(2^2)^2                 |
 x+Z(2^2)                 |
 x+Z(2^2)^2               |
 Z(2^2)*x+Z(2)^0          |
 Z(2^2)*x+Z(2^2)          |
 Z(2^2)*x+Z(2^2)^2        |
 Z(2^2)^2*x+Z(2)^0        |
 Z(2^2)^2*x+Z(2^2)        |
 Z(2^2)^2*x+Z(2^2)^2      | P
 x+Z(2)^0                 | (P + x+Z(2)^0)/x

gap> last^2;
IdentityMapping( GF(2^2)[x] )
gap> IsRcwaMapping(last);
true
gap> ct := ClassTransposition(-100,2,141,20);
GeneralizedClassTransposition(-100,2,141,20)
gap> IsGeneralizedClassTransposition(ct);
true
gap> IsClassTransposition(ct);
false
gap> Sign(ct);
1
gap> Factorization(ct);
[ ClassShift(1,20)^-57, ClassShift(0,2)^57, ClassTransposition(0,2,1,20) ]
gap> Product(last)/ct;
IdentityMapping( Integers )
gap> TransposedClasses(ct);
[ [-100/2], [141/20] ]
gap> ct = ClassTransposition(last);
true
gap> RCWADoThingsToBeDoneAfterTest();
gap> STOP_TEST( "cscrct.tst", 900000000 );

#############################################################################
##
#E  cscrct.tst . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here