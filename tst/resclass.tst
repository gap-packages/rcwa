#############################################################################
##
#W  resclass.tst               GAP4 Package `RCWA'                Stefan Kohl
##
#H  @(#)$Id$
##
#Y  Copyright (C) 2002 by Stefan Kohl, Mathematisches Institut B,
#Y  Universit\"at Stuttgart, Germany
##

gap> START_TEST("$Id$");
gap> A := ResidueClass(Integers,3,2);
The residue class 2(3)
gap> B := ResidueClass(Z_pi([2,5]),2,1);
The residue class 1(2) of Z_[ 2, 5 ]
gap> B = ResidueClass(Integers,2,1);
false
gap> R := PolynomialRing(GF(7),1);;
gap> x := Indeterminate(GF(7),1);; SetName(x,"x");
gap> C := ResidueClass(R,x+One(R),3*One(R));
The residue class Z(7) ( mod x+Z(7)^0 ) of GF(7)[x]
gap> D := ResidueClassUnion(Integers,6,[2,4]);
Union of the residue classes 2(6) and 4(6)
gap> F := ResidueClassUnion(Integers,5,[1,2],[3,8],[-4,1]);
Union of the residue classes 1(5) and 2(5), +2/-2 elements
gap> G := ResidueClassUnion(R,x,[One(R),5*One(R),6*One(R)],[Zero(R)],[One(R)]);
<union of 3 residue classes (mod x) of GF(7)[x], +1/-1 elements>
gap> H := ResidueClassUnion(Z_pi([2,3]),8,[3,5]);
<union of 2 residue classes (mod 8) of Z_[ 2, 3 ]>
gap> Modulus(F);
5
gap> Modulus(G);
x
gap> Modulus(H);
8
gap> Residues(A);
[ 2 ]
gap> Residues(F);
[ 1, 2 ]
gap> Residues(G);
[ Z(7)^0, -Z(7)^0, Z(7)^5 ]
gap> Residues(H);
[ 3, 5 ]
gap> IncludedElements(F);
[ 3, 8 ]
gap> IncludedElements(G);
[ 0*Z(7) ]
gap> IncludedElements(H);
[  ]
gap> ExcludedElements(F);
[ -4, 1 ]
gap> ExcludedElements(G);
[ Z(7)^0 ]
gap> ExcludedElements(H);
[  ]
gap> String(C);
"ResidueClassUnion( GF(7)[x], x+Z(7)^0, [ Z(7) ] )"
gap> String(F);
"ResidueClassUnion( Integers, 5, [ 1, 2 ], [ 3, 8 ], [ -4, 1 ] )"
gap> String(H);
"ResidueClassUnion( Z_[ 2, 3 ], 8, [ 3, 5 ] )"
gap> Print(C,"\n");
ResidueClassUnion( GF(7)[x], x+Z(7)^0, [ Z(7) ] )
gap> Print(F,"\n");
ResidueClassUnion( Integers, 5, [ 1, 2 ], [ 3, 8 ], [ -4, 1 ] )
gap> Print(H,"\n");
ResidueClassUnion( Z_[ 2, 3 ], 8, [ 3, 5 ] )
gap> Display(F);

The union of the residue classes r ( mod 5 )  for r =

 1 2

and the elements

 3 8

without the elements

 -4  1

gap> Display(G);

The union of the residue classes r ( mod x ) of GF(7)[x] for r =

Z(7)^0  -Z(7)^0 Z(7)^5  

and the element

0*Z(7) 

without the element

Z(7)^0 

gap> Display(H);

The union of the residue classes r ( mod 8 ) of Z_[ 2, 3 ] for r =

 3 5

gap> 20 in A;
true
gap> -20 in A;
false
gap> 1/3 in B;
true
gap> x in G;
false
gap> Zero(R) in G;
true
gap> IsSubset(A,D);
false
gap> IsSubset(H,ResidueClass(Z_pi([2,3]),16,11));
true
gap> Difference([2,4,7,8],A);
[ 4, 7 ]
gap> Complement(A);
Union of the residue classes 0(3) and 1(3)
gap> Complement(B);
The residue class 0(2) of Z_[ 2, 5 ]
gap> Complement(C);
<union of 6 residue classes (mod x+Z(7)^0) of GF(7)[x]>
gap> Complement(F);
Union of the residue classes 0(5), 3(5) and 4(5), +2/-2 elements
gap> Complement(H);
<union of 6 residue classes (mod 8) of Z_[ 2, 3 ]>
gap> I := ResidueClassUnion(Integers,6,[1,5]);
Union of the residue classes 1(6) and 5(6)
gap> J := ResidueClassUnion(Integers,5,[1,2,3,4]);
Union of the residue classes 1(5), 2(5), 3(5) and 4(5)
gap> K := Union(I,J);
<union of 26 residue classes (mod 30)>
gap> Residues(K);
[ 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19, 21, 22, 23, 24, 
  25, 26, 27, 28, 29 ]
gap> L := Intersection(I,J);
<union of 8 residue classes (mod 30)>
gap> Display(L);

The union of the residue classes r ( mod 30 )  for r =

  1  7 11 13 17 19 23 29

gap> M := Difference(I,J);
Union of the residue classes 5(30) and 25(30)
gap> N := Difference(J,I);
<union of 16 residue classes (mod 30)>
gap> Display(N);

The union of the residue classes r ( mod 30 )  for r =

  2  3  4  6  8  9 12 14 16 18 21 22 24 26 27 28

gap> Difference(Integers,[1,2,3]);
Integers \ [ 1, 2, 3 ]
gap> Display(last);
Integers \ [ 1, 2, 3 ]
gap> Difference(Z_pi([2,3,7]),[1/5,1/55]);
Z_[ 2, 3, 7 ] \ [ 1/55, 1/5 ]
gap> O := Difference(Union(A,[1,3]),[2,5,8]);
The residue class 2(3), +2/-3 elements
gap> P := Union(Difference(A,[-1]),[-3,0]);
The residue class 2(3), +2/-1 elements
gap> Display(Union(O,P));

The residue class 2 ( mod 3 )

and the elements

 -3  0  1  3

gap> Difference(O,P);
[ -1, 1, 3 ]
gap> Difference(P,O);
[ -3, 0, 2, 5, 8 ]
gap> Display(Union(A,[1..100]));

The residue class 2 ( mod 3 )

and the elements

   1   3   4   6   7   9  10  12  13  15  16  18  19  21  22  24  25  27  28
  30  31  33  34  36  37  39  40  42  43  45  46  48  49  51  52  54  55  57
  58  60  61  63  64  66  67  69  70  72  73  75  76  78  79  81  82  84  85
  87  88  90  91  93  94  96  97  99 100

gap> Display(Difference(A,[1..100]));

The residue class 2 ( mod 3 )

without the elements

  2  5  8 11 14 17 20 23 26 29 32 35 38 41 44 47 50 53 56 59 62 65 68 71 74
 77 80 83 86 89 92 95 98

gap> Union(A,Complement(A));
Integers
gap> Union(B,Complement(B));
Z_[ 2, 5 ]
gap> Union(C,Complement(C));
GF(7)[x]
gap> Q := ResidueClassUnion( Integers, 18, [ 2, 5, 8, 11, 14, 16, 17 ],
>                            [ 1, 3, 4, 10 ], [ 2, 5, 8, 16 ] );;
gap> IsSubset(Q,O);
true
gap> IsSubset(O,Q);
false
gap> U := ResidueClassUnion(Integers,3,[1],[0],[]);
The residue class 1(3), +1/-0 elements
gap> V := ResidueClassUnion(Integers,3,[2],[0],[]);
The residue class 2(3), +1/-0 elements
gap> Intersection(U,V);
[ 0 ]
gap> U := ResidueClassUnion(Integers,3,[1],[0],[1]);
The residue class 1(3), +1/-1 elements
gap> V := ResidueClassUnion(Integers,3,[1,2],[0],[]);
Union of the residue classes 1(3) and 2(3), +1/-0 elements
gap> Display(Difference(V,U));
 
The residue class 2 ( mod 3 )
 
and the element
 
 1

gap> cl := List([1..25],i->ResidueClass(Integers,Primes[i],i));;
gap> cl_int := Intersection(cl);
The residue class 941584379775558526136539054851975983(
2305567963945518424753102147331756070)
gap> List(Primes{[1..25]},p->Representative(cl_int) mod p);
[ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 
  22, 23, 24, 25 ]
gap> it := Iterator(F);
<iterator of a residue class union of Z>
gap> l := List([1..16],i->NextIterator(it));
[ 3, 8, 2, -3, 6, -9, 7, -8, 11, -14, 12, -13, 16, -19, 17, -18 ]
gap> it2 := ShallowCopy(it);
<iterator of a residue class union of Z>
gap> l := List([1..16],i->NextIterator(it2));
[ 21, -24, 22, -23, 26, -29, 27, -28, 31, -34, 32, -33, 36, -39, 37, -38 ]
gap> l := [];;
gap> for n in F do Add(l,n); if Length(l) > 100 then break; fi; od;
gap> Set(l) = Intersection(F,[-124..126]);
true
gap> l := [];;
gap> for n in Complement(A) do Add(l,n); if Length(l)>100 then break; fi; od;
gap> Set(l) = Intersection(Complement(A),[-75..75]);
true
gap> STOP_TEST( "resclass.tst", 200000000 );

#############################################################################
##
#E  resclass.tst . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
