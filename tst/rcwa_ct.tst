#############################################################################
##
#W  rcwa_ct.tst                GAP4 Package `RCWA'                Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains automated tests of RCWA's specialized functionality
##  for the groups RCWA(R) and CT(R).
##
gap> START_TEST("$Id$");
gap> oldformat := RESCLASSES_VIEWING_FORMAT;;
gap> oldwarninglevel := InfoLevel(InfoWarning);;
gap> SetInfoLevel(InfoWarning,0);
gap> ResidueClassUnionViewingFormat("short");
gap> G := RCWA(Integers);
RCWA(Z)
gap> Set(KnownPropertiesOfObject(G));
[ "IsAssociative", "IsCommutative", "IsDuplicateFree", "IsEmpty", "IsFinite", 
  "IsFinitelyGeneratedGroup", "IsNaturalRCWA", "IsNaturalRCWA_OR_CT", 
  "IsNaturalRCWA_Z", "IsNonTrivial", "IsPerfectGroup", "IsSimpleGroup", 
  "IsSimpleSemigroup", "IsSolvableGroup", "IsTrivial" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ true, false, true, false, false, false, true, true, true, true, false, 
  false, true, false, false ]
gap> Set(KnownAttributesOfObject(G));
[ "Centre", "Divisor", "ModulusOfRcwaGroup", "MultiplicativeNeutralElement", 
  "Multiplier", "Name", "OneImmutable", "Representative", "Size", 
  "StructureDescription" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ Trivial rcwa group over Z, infinity, 0, IdentityMapping( Integers ), 
  infinity, "RCWA(Z)", IdentityMapping( Integers ), 
  Rcwa mapping of Z: n -> -n, infinity, "RCWA(Z)" ]
gap> One(G) in G;
true
gap> Random(G) in G;
true
gap> StructureDescription(RCWA(Integers));
"RCWA(Z)"
gap> NrConjugacyClassesOfRCWAZOfOrder(2);
infinity
gap> NrConjugacyClassesOfRCWAZOfOrder(105);
218
gap> RepresentativeAction(RCWA(Integers),-6,13,OnPoints);
ClassShift(0,1)^19
gap> elm := RepresentativeAction(RCWA(Integers),[0,-7,1,2],[7,1,3,0],
>                                OnTuples);
<bijective rcwa mapping of Z with modulus 15, of order 18>
gap> OnTuples([0,-7,1,2],elm);
[ 7, 1, 3, 0 ]
gap> elm := RepresentativeAction(RCWA(Integers),ResidueClass(1,2),
>                                ResidueClassUnion(Integers,5,[2,3]));;
gap> ResidueClass(1,2)^elm;
2(5) U 3(5)
gap> P1 := List([[0,2],[1,4],[3,4]],ResidueClass);
[ 0(2), 1(4), 3(4) ]
gap> P2 := AllResidueClassesModulo(3);
[ 0(3), 1(3), 2(3) ]
gap> elm := RepresentativeAction(RCWA(Integers),P1,P2);
<bijective rcwa mapping of Z with modulus 4>
gap> P1^elm = P2;
true
gap> elmt := RepresentativeAction(RCWA(Integers),P1,P2:IsTame);
<tame bijective rcwa mapping of Z with modulus 24>
gap> P1^elmt = P2;
true
gap> P1 := [ResidueClass(1,3),Union(ResidueClass(0,3),ResidueClass(2,3))];;
gap> P2 := [Union(List([[2,5],[4,5]],ResidueClass)),
>           Union(List([[0,5],[1,5],[3,5]],ResidueClass))];;
gap> elm := RepresentativeAction(RCWA(Integers),P1,P2);
<bijective rcwa mapping of Z with modulus 6>
gap> P1^elm;
[ 2(5) U 4(5), Z \ 2(5) U 4(5) ]
gap> elmt := RepresentativeAction(RCWA(Integers),P1,P2:IsTame);
<tame bijective rcwa mapping of Z with modulus 120>
gap> P1^elmt;
[ 2(5) U 4(5), Z \ 2(5) U 4(5) ]
gap> Modulus(RepresentativeAction(RCWA(Integers),
>            ClassShift(0,2) * ClassTransposition(1,6,3,18)
>          * ClassShift(5,12)^-1 * ClassReflection(11,12),
>            ClassShift(3,5) * ClassTransposition(2,5,1,10)
>          * ClassShift(4,10) * ClassReflection(9,10)));
36
gap> G := RCWA(Z_pi([2,3]));
RCWA(Z_( 2, 3 ))
gap> Set(KnownPropertiesOfObject(G));
[ "IsAssociative", "IsCommutative", "IsDuplicateFree", "IsEmpty", "IsFinite", 
  "IsNaturalRCWA", "IsNaturalRCWA_OR_CT", "IsNaturalRCWA_Z_pi", 
  "IsNonTrivial", "IsSimpleSemigroup", "IsSolvableGroup", "IsTrivial" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ true, false, true, false, false, true, true, true, true, true, false, false 
 ]
gap> Set(KnownAttributesOfObject(G));
[ "Centre", "Divisor", "ModulusOfRcwaGroup", "MultiplicativeNeutralElement", 
  "Multiplier", "Name", "OneImmutable", "Representative", "Size", 
  "StructureDescription" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ Trivial rcwa group over Z_( 2, 3 ), infinity, 0, 
  IdentityMapping( Z_( 2, 3 ) ), infinity, "RCWA(Z_( 2, 3 ))", 
  IdentityMapping( Z_( 2, 3 ) ), Rcwa mapping of Z_( 2, 3 ): n -> -n, 
  infinity, "RCWA(Z_( 2, 3 ))" ]
gap> One(G) in G;
true
gap> Random(G) in G;
true
gap> P1 := RandomPartitionIntoResidueClasses(Z_pi([2,3]),5,[2,3]);;
gap> P2 := RandomPartitionIntoResidueClasses(Z_pi([2,3]),5,[2,3]);;
gap> elm := RepresentativeAction(G,P1,P2);;
gap> P1^elm = P2;
true
gap> S1 := ResidueClassUnion(Z_pi([2,3]),3,[1,2]);
Z_( 2, 3 ) \ 0(3)
gap> S2 := ResidueClassUnion(Z_pi([2,3]),8,[3,6,7]);
3(4) U 6(8)
gap> elm := RepresentativeAction(G,S1,S2);
<bijective rcwa mapping of Z_( 2, 3 ) with modulus 12>
gap> S1^elm = S2;
true
gap> x := Indeterminate(GF(2),1);; SetName(x,"x");
gap> R := PolynomialRing(GF(2),1);
GF(2)[x]
gap> G := RCWA(R);
RCWA(GF(2)[x])
gap> Set(KnownPropertiesOfObject(G));
[ "IsAssociative", "IsCommutative", "IsDuplicateFree", "IsEmpty", "IsFinite", 
  "IsFinitelyGeneratedGroup", "IsNaturalRCWA", "IsNaturalRCWA_GFqx", 
  "IsNaturalRCWA_OR_CT", "IsNonTrivial", "IsSimpleSemigroup", 
  "IsSolvableGroup", "IsTrivial" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ true, false, true, false, false, false, true, true, true, true, true, 
  false, false ]
gap> Set(KnownAttributesOfObject(G));
[ "Centre", "Divisor", "ModulusOfRcwaGroup", "MultiplicativeNeutralElement", 
  "Multiplier", "Name", "OneImmutable", "Representative", "Size", 
  "StructureDescription" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ Trivial rcwa group over GF(2)[x], infinity, 0*Z(2), 
  IdentityMapping( GF(2)[x] ), infinity, "RCWA(GF(2)[x])", 
  IdentityMapping( GF(2)[x] ), ClassTransposition(0*Z(2),x,Z(2)^0,x), 
  infinity, "RCWA(GF(2)[x])" ]
gap> One(G) in G;
true
gap> Random(G) in G;
true
gap> ct := ClassTransposition(Zero(R),x,One(R),x^2);
ClassTransposition(0*Z(2),x,Z(2)^0,x^2)
gap> IsSubgroup(RCWA(R),Group(ct));
true
gap> P1 := RespectedPartition(ct);
[ 0*Z(2)(mod x), Z(2)^0(mod x^2), x+Z(2)^0(mod x^2) ]
gap> P2 := Permuted(P1,ct);
[ Z(2)^0(mod x^2), 0*Z(2)(mod x), x+Z(2)^0(mod x^2) ]
gap> g := RepresentativeAction(RCWA(R),P1,P2);
<bijective rcwa mapping of GF(2)[x] with modulus x^2>
gap> P1^g = P2;
true
gap> cls := AllResidueClassesModulo(R,x^3);;
gap> S1 := Union(cls{[1,4,8]});
x+Z(2)^0(mod x^2) U x^2+x+Z(2)^0(mod x^3)
gap> S2 := Union(cls{[1,7]});
0*Z(2)(mod x^3) U x^2+x(mod x^3)
gap> elm := RepresentativeAction(G,S1,S2);
<bijective rcwa mapping of GF(2)[x] with modulus x^3>
gap> S1^elm = S2;
true
gap> G := CT(Integers);
CT(Z)
gap> Set(KnownPropertiesOfObject(G));
[ "IsAssociative", "IsCommutative", "IsDuplicateFree", "IsEmpty", "IsFinite", 
  "IsFinitelyGeneratedGroup", "IsNaturalCT", "IsNaturalCT_Z", 
  "IsNaturalRCWA_OR_CT", "IsNonTrivial", "IsPerfectGroup", "IsSimpleGroup", 
  "IsSimpleSemigroup", "IsSolvableGroup", "IsTrivial" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ true, false, true, false, false, false, true, true, true, true, true, true, 
  true, false, false ]
gap> Set(KnownAttributesOfObject(G));
[ "Centre", "Divisor", "ModulusOfRcwaGroup", "MultiplicativeNeutralElement", 
  "Multiplier", "Name", "OneImmutable", "Representative", "Size", 
  "StructureDescription", "Support" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ Trivial rcwa group over Z, infinity, 0, IdentityMapping( Integers ), 
  infinity, "CT(Z)", IdentityMapping( Integers ), ClassTransposition(0,2,1,2), 
  infinity, "CT(Z)", Integers ]
gap> One(G) in G;
true
gap> Random(G) in G;
true
gap> H := Group(ClassTransposition(0,2,1,4)  * ClassTransposition(1,3,5,9),
>               ClassTransposition(4,6,2,12) * ClassTransposition(2,6,7,12));;
gap> IsSubgroup(G,H);
true
gap> H := ClosureGroup(H,ClassReflection(0,3)^ClassShift(0,2));;
gap> IsSubgroup(G,H);
false
gap> conj := RepresentativeAction(CT(Integers),ClassTransposition(1,4,2,6),
>                                              ClassTransposition(2,8,3,10));
<bijective rcwa mapping of Z with modulus 480>
gap> ClassTransposition(1,4,2,6)^conj = ClassTransposition(2,8,3,10);
true
gap> Factorization(conj);
[ ClassTransposition(1,4,3,8), ClassTransposition(2,6,7,8),
  ClassTransposition(0,4,3,8), ClassTransposition(6,8,7,8),
  ClassTransposition(0,4,2,8), ClassTransposition(6,8,3,10) ]
gap> conj = Product(last);
true
gap> G := CT(Z_pi([2,3]));
CT(Z_( 2, 3 ))
gap> Set(KnownPropertiesOfObject(G));
[ "IsAssociative", "IsCommutative", "IsDuplicateFree", "IsEmpty", "IsFinite", 
  "IsNaturalCT", "IsNaturalCT_Z_pi", "IsNaturalRCWA_OR_CT", "IsNonTrivial", 
  "IsSimpleSemigroup", "IsSolvableGroup", "IsTrivial" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ true, false, true, false, false, true, true, true, true, true, false, false 
 ]
gap> Set(KnownAttributesOfObject(G));
[ "Centre", "Divisor", "ModulusOfRcwaGroup", "MultiplicativeNeutralElement", 
  "Multiplier", "Name", "OneImmutable", "Representative", "Size", 
  "StructureDescription", "Support" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ Trivial rcwa group over Z_( 2, 3 ), infinity, 0, 
  IdentityMapping( Z_( 2, 3 ) ), infinity, "CT(Z_( 2, 3 ))", 
  IdentityMapping( Z_( 2, 3 ) ), ClassTransposition(0,2,1,2), infinity, 
  "CT(Z_( 2, 3 ))", Z_( 2, 3 ) ]
gap> One(G) in G;
true
gap> Random(G) in G;
true
gap> Zpi := Z_pi([2,3]);
Z_( 2, 3 )
gap> ct1 := ClassTransposition(ResidueClass(Zpi,4,0),ResidueClass(Zpi,6,1));
ClassTransposition(0,4,1,6)
gap> ct2 := ClassTransposition(ResidueClass(Zpi,2,1),ResidueClass(Zpi,4,2));
ClassTransposition(1,2,2,4)
gap> elm := RepresentativeAction(G,ct1,ct2);
<bijective rcwa mapping of Z_( 2, 3 ) with modulus 48>
gap> ct1^elm = ct2;
true
gap> Factorization(elm);
[ ClassTransposition(0,4,2,16), ClassTransposition(1,6,10,16),
  ClassTransposition(0,8,2,16), ClassTransposition(4,8,10,16),
  ClassTransposition(1,2,0,8), ClassTransposition(2,4,4,8) ]
gap> IsSubset(G,last);
true
gap> G := CT(R);
CT(GF(2)[x])
gap> Set(KnownPropertiesOfObject(G));
[ "IsAssociative", "IsCommutative", "IsDuplicateFree", "IsEmpty", "IsFinite", 
  "IsFinitelyGeneratedGroup", "IsNaturalCT", "IsNaturalCT_GFqx", 
  "IsNaturalRCWA_OR_CT", "IsNonTrivial", "IsSimpleSemigroup", 
  "IsSolvableGroup", "IsTrivial" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ true, false, true, false, false, false, true, true, true, true, true, 
  false, false ]
gap> Set(KnownAttributesOfObject(G));
[ "Centre", "Divisor", "ModulusOfRcwaGroup", "MultiplicativeNeutralElement", 
  "Multiplier", "Name", "OneImmutable", "Representative", "Size", 
  "StructureDescription", "Support" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ Trivial rcwa group over GF(2)[x], infinity, 0*Z(2), 
  IdentityMapping( GF(2)[x] ), infinity, "CT(GF(2)[x])", 
  IdentityMapping( GF(2)[x] ), ClassTransposition(0*Z(2),x,Z(2)^0,x), 
  infinity, "CT(GF(2)[x])", GF(2)[x] ]
gap> One(G) in G;
true
gap> Random(G) in G;
true
gap> IsSubgroup(G,Group(ClassTransposition(Zero(R),x,One(R),x)));
true
gap> ct1 := ClassTransposition(One(R),x,x,x^2+x);
ClassTransposition(Z(2)^0,x,x,x^2+x)
gap> ct2 := ClassTransposition(One(R),x^2,x,x^2+x);
ClassTransposition(Z(2)^0,x^2,x,x^2+x)
gap> elm := RepresentativeAction(G,ct1,ct2);
<bijective rcwa mapping of GF(2)[x] with modulus x^5+x^4>
gap> ct1^elm = ct2;
true
gap> Factorization(elm);
[ ClassTransposition(Z(2)^0,x,0*Z(2),x^4+x^3),
  ClassTransposition(x,x^2+x,x^3+x^2,x^4+x^3),
  ClassTransposition(x+Z(2)^0,x^2,0*Z(2),x^4+x^3),
  ClassTransposition(x^2+x,x^3+x^2,x^3+x^2,x^4+x^3),
  ClassTransposition(Z(2)^0,x^2,x+Z(2)^0,x^2),
  ClassTransposition(x,x^2+x,x^2+x,x^3+x^2) ]
gap> SetInfoLevel(InfoWarning,oldwarninglevel);
gap> ResidueClassUnionViewingFormat(oldformat);
gap> STOP_TEST( "rcwa_ct.tst", 1100000000 );

#############################################################################
##
#E  rcwa_ct.tst . . . . . . . . . . . . . . . . . . . . . . . . . . ends here