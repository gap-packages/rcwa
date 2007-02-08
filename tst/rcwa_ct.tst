#############################################################################
##
#W  rcwa_ct.tst                GAP4 Package `RCWA'                Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains tests of RCWA's specialized functionality for the
##  groups RCWA(R) and CT(R).
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
  "MultiplicativeNeutralElement", "Centre", "Multiplier", "Divisor", 
  "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "RCWA(Z)", infinity, Rcwa mapping of Z: n -> -n, 
  IdentityMapping( Integers ), IdentityMapping( Integers ), 
  Trivial rcwa group over Z, infinity, infinity, 0 ]
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
  "MultiplicativeNeutralElement", "Centre", "Multiplier", "Divisor", 
  "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "RCWA(Z_( 2, 3 ))", infinity, Rcwa mapping of Z_( 2, 3 ): n -> -n, 
  IdentityMapping( Z_( 2, 3 ) ), IdentityMapping( Z_( 2, 3 ) ), 
  Trivial rcwa group over Z_( 2, 3 ), infinity, infinity, 0 ]
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
  "MultiplicativeNeutralElement", "Centre", "Multiplier", "Divisor", 
  "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "RCWA(GF(2)[x])", infinity, IdentityMapping( GF(2)[x] ), 
  IdentityMapping( GF(2)[x] ), IdentityMapping( GF(2)[x] ), 
  Trivial rcwa group over GF(2)[x], infinity, infinity, 0*Z(2) ]
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
  "MultiplicativeNeutralElement", "Centre", "Support", "Multiplier", 
  "Divisor", "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "CT(Z)", infinity, ClassTransposition(0,2,1,2), IdentityMapping( Integers ),
  IdentityMapping( Integers ), Trivial rcwa group over Z, Integers, infinity, 
  infinity, 0 ]
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
  "MultiplicativeNeutralElement", "Centre", "Support", "Multiplier", 
  "Divisor", "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "CT(Z_( 2, 3 ))", infinity, ClassTransposition(0,2,1,2), 
  IdentityMapping( Z_( 2, 3 ) ), IdentityMapping( Z_( 2, 3 ) ), 
  Trivial rcwa group over Z_( 2, 3 ), Z_( 2, 3 ), infinity, infinity, 0 ]
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
  "MultiplicativeNeutralElement", "Centre", "Support", "Multiplier", 
  "Divisor", "ModulusOfRcwaGroup" ]
gap> List(last,attr->ValueGlobal(attr)(G));
[ "CT(GF(2)[x])", infinity, ClassTransposition(0*Z(2),x,Z(2)^0,x), 
  IdentityMapping( GF(2)[x] ), IdentityMapping( GF(2)[x] ), 
  Trivial rcwa group over GF(2)[x], GF(2)[x], infinity, infinity, 0*Z(2) ]
gap> SetInfoLevel(InfoWarning,oldwarninglevel);
gap> ResidueClassUnionViewingFormat(oldformat);
gap> STOP_TEST( "RCWA_CT.tst", 100000000 );

#############################################################################
##
#E  rcwa_ct.tst . . . . . . . . . . . . . . . . . . . . . . . . . . ends here