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
gap> KnownPropertiesOfObject(G);
[ "IsEmpty", "IsTrivial", "IsNonTrivial", "IsFinite", "IsDuplicateFree", 
  "IsAssociative", "IsCommutative", "IsSimpleSemigroup", 
  "IsFinitelyGeneratedGroup", "IsPerfectGroup", "IsSimpleGroup", 
  "IsSolvableGroup", "IsNaturalRCWA", "IsNaturalRCWA_Z", 
  "IsNaturalRCWA_OR_CT" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ false, false, true, false, true, true, false, true, false, false, false, 
  false, true, true, true ]
gap> KnownAttributesOfObject(G);
[ "Name", "Size", "Representative", "OneImmutable", 
  "MultiplicativeNeutralElement", "Centre", "StructureDescription", 
  "Multiplier", "Divisor", "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "RCWA(Z)", infinity, Rcwa mapping of Z: n -> -n, 
  IdentityMapping( Integers ), IdentityMapping( Integers ), 
  Trivial rcwa group over Z, "RCWA(Z)", infinity, infinity, 0 ]
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
gap> KnownPropertiesOfObject(G);
[ "IsEmpty", "IsTrivial", "IsNonTrivial", "IsFinite", "IsDuplicateFree", 
  "IsAssociative", "IsCommutative", "IsSimpleSemigroup", "IsSolvableGroup", 
  "IsNaturalRCWA", "IsNaturalRCWA_Z_pi", "IsNaturalRCWA_OR_CT" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ false, false, true, false, true, true, false, true, false, true, true, true 
 ]
gap> KnownAttributesOfObject(G);
[ "Name", "Size", "Representative", "OneImmutable",
  "MultiplicativeNeutralElement", "Centre", "StructureDescription",
  "Multiplier", "Divisor", "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "RCWA(Z_( 2, 3 ))", infinity, Rcwa mapping of Z_( 2, 3 ): n -> -n, 
  IdentityMapping( Z_( 2, 3 ) ), IdentityMapping( Z_( 2, 3 ) ), 
  Trivial rcwa group over Z_( 2, 3 ), "RCWA(Z_( 2, 3 ))", infinity, infinity, 
  0 ]
gap> One(G) in G;
true
gap> Random(G) in G;
true
gap> x := Indeterminate(GF(2),1);; SetName(x,"x");
gap> R := PolynomialRing(GF(2),1);
GF(2)[x]
gap> G := RCWA(R);
RCWA(GF(2)[x])
gap> KnownPropertiesOfObject(G);
[ "IsEmpty", "IsTrivial", "IsNonTrivial", "IsFinite", "IsDuplicateFree", 
  "IsAssociative", "IsCommutative", "IsSimpleSemigroup", 
  "IsFinitelyGeneratedGroup", "IsSolvableGroup", "IsNaturalRCWA", 
  "IsNaturalRCWA_GFqx", "IsNaturalRCWA_OR_CT" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ false, false, true, false, true, true, false, true, false, false, true, 
  true, true ]
gap> KnownAttributesOfObject(G);
[ "Name", "Size", "Representative", "OneImmutable", 
  "MultiplicativeNeutralElement", "Centre", "StructureDescription", 
  "Multiplier", "Divisor", "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "RCWA(GF(2)[x])", infinity, ClassTransposition(0*Z(2),x,Z(2)^0,x), 
  IdentityMapping( GF(2)[x] ), IdentityMapping( GF(2)[x] ), 
  Trivial rcwa group over GF(2)[x], "RCWA(GF(2)[x])", infinity, infinity, 
  0*Z(2) ]
gap> One(G) in G;
true
gap> Random(G) in G;
true
gap> ct := ClassTransposition(ResidueClass(R,x,Zero(R)),
>                             ResidueClass(R,x^2,One(R)));
ClassTransposition(0*Z(2),x,Z(2)^0,x^2)
gap> P1 := RespectedPartition(ct);
[ 0*Z(2)(mod x), Z(2)^0(mod x^2), x+Z(2)^0(mod x^2) ]
gap> P2 := Permuted(P1,ct);
[ Z(2)^0(mod x^2), 0*Z(2)(mod x), x+Z(2)^0(mod x^2) ]
gap> g := RepresentativeAction(RCWA(R),P1,P2);
<bijective rcwa mapping of GF(2)[x] with modulus x^2>
gap> P1^g = P2;
true
gap> G := CT(Integers);
CT(Z)
gap> KnownPropertiesOfObject(G);
[ "IsEmpty", "IsTrivial", "IsNonTrivial", "IsFinite", "IsDuplicateFree", 
  "IsAssociative", "IsCommutative", "IsSimpleSemigroup", 
  "IsFinitelyGeneratedGroup", "IsPerfectGroup", "IsSimpleGroup", 
  "IsSolvableGroup", "IsNaturalCT", "IsNaturalCT_Z", "IsNaturalRCWA_OR_CT" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ false, false, true, false, true, true, false, true, false, true, true, 
  false, true, true, true ]
gap> KnownAttributesOfObject(G);
[ "Name", "Size", "Representative", "OneImmutable", 
  "MultiplicativeNeutralElement", "Centre", "StructureDescription", 
  "Support", "Multiplier", "Divisor", "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "CT(Z)", infinity, ClassTransposition(0,2,1,2), IdentityMapping( Integers ),
  IdentityMapping( Integers ), Trivial rcwa group over Z, "CT(Z)", Integers, 
  infinity, infinity, 0 ]
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
gap> KnownPropertiesOfObject(G);
[ "IsEmpty", "IsTrivial", "IsNonTrivial", "IsFinite", "IsDuplicateFree", 
  "IsAssociative", "IsCommutative", "IsSimpleSemigroup", "IsSolvableGroup", 
  "IsNaturalCT", "IsNaturalCT_Z_pi", "IsNaturalRCWA_OR_CT" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ false, false, true, false, true, true, false, true, false, true, true, true 
 ]
gap> KnownAttributesOfObject(G);
[ "Name", "Size", "Representative", "OneImmutable", 
  "MultiplicativeNeutralElement", "Centre", "StructureDescription", 
  "Support", "Multiplier", "Divisor", "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "CT(Z_( 2, 3 ))", infinity, ClassTransposition(0,2,1,2), 
  IdentityMapping( Z_( 2, 3 ) ), IdentityMapping( Z_( 2, 3 ) ), 
  Trivial rcwa group over Z_( 2, 3 ), "CT(Z_( 2, 3 ))", Z_( 2, 3 ), infinity, 
  infinity, 0 ]
gap> One(G) in G;
true
gap> Random(G) in G;
true
gap> G := CT(R);
CT(GF(2)[x])
gap> KnownPropertiesOfObject(G);
[ "IsEmpty", "IsTrivial", "IsNonTrivial", "IsFinite", "IsDuplicateFree", 
  "IsAssociative", "IsCommutative", "IsSimpleSemigroup", 
  "IsFinitelyGeneratedGroup", "IsSolvableGroup", "IsNaturalCT", 
  "IsNaturalCT_GFqx", "IsNaturalRCWA_OR_CT" ]
gap> List(last,prop->ValueGlobal(prop)(G));
[ false, false, true, false, true, true, false, true, false, false, true, 
  true, true ]
gap> KnownAttributesOfObject(G);
[ "Name", "Size", "Representative", "OneImmutable", 
  "MultiplicativeNeutralElement", "Centre", "StructureDescription", 
  "Support", "Multiplier", "Divisor", "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "CT(GF(2)[x])", infinity, ClassTransposition(0*Z(2),x,Z(2)^0,x), 
  IdentityMapping( GF(2)[x] ), IdentityMapping( GF(2)[x] ), 
  Trivial rcwa group over GF(2)[x], "CT(GF(2)[x])", GF(2)[x], infinity, 
  infinity, 0*Z(2) ]
gap> One(G) in G;
true
gap> Random(G) in G;
true
gap> SetInfoLevel(InfoWarning,oldwarninglevel);
gap> ResidueClassUnionViewingFormat(oldformat);
gap> STOP_TEST( "rcwa_ct.tst", 100000000 );

#############################################################################
##
#E  rcwa_ct.tst . . . . . . . . . . . . . . . . . . . . . . . . . . ends here