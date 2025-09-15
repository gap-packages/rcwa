#############################################################################
##
#W  rcwagrp.gd                GAP4 Package `RCWA'                 Stefan Kohl
##
##  This file contains declarations of functions, operations etc. for
##  computing with rcwa groups.
##
##  See the definitions given in the file rcwamap.gd.
##
#############################################################################

#############################################################################
##
#S  Basic definitions. //////////////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#C  CategoryCollections( IsRcwaMappingOfZ ) . . . . . . . rcwa domains over Z
##
##  The category of all domains formed out of rcwa mappings of Z.
##
DeclareCategoryCollections( "IsRcwaMappingOfZ" );

#############################################################################
##
#C  IsRcwaGroupOverZ . . . . . . . . . . . . . . . . . . . rcwa groups over Z
#C  IsRcwaGroupOverZxZ . . . . . . . . . . . . . . . . . rcwa groups over Z^2
#C  IsRcwaGroupOverZ_pi . . . . . . . . . . . . . . . rcwa groups over Z_(pi)
#C  IsRcwaGroupOverGFqx . . . . . . . . . . . . . . rcwa groups over GF(q)[x]
#C  IsRcwaGroupOverZOrZ_pi . . . . . . . . . . . rcwa groups over Z or Z_(pi)
##
##  The category of all rcwa groups over Z, over Z^2, over semilocalizations
##  of Z or over polynomial rings in one variable over a finite field,
##  respectively. The category `IsRcwaGroupOverZOrZ_pi' is the union of
##  `IsRcwaGroupOverZ' and `IsRcwaGroupOverZ_pi'.
##
DeclareSynonym( "IsRcwaGroupOverZ",
                 CategoryCollections(IsRcwaMappingOfZ) and IsGroup );
DeclareSynonym( "IsRcwaGroupOverZxZ",
                 CategoryCollections(IsRcwaMappingOfZxZ) and IsGroup );
DeclareSynonym( "IsRcwaGroupOverZ_pi",
                 CategoryCollections(IsRcwaMappingOfZ_pi) and IsGroup );
DeclareSynonym( "IsRcwaGroupOverGFqx",
                 CategoryCollections(IsRcwaMappingOfGFqx) and IsGroup );
DeclareSynonym( "IsRcwaGroupOverZOrZ_pi",
                 CategoryCollections(IsRcwaMappingOfZOrZ_pi) and IsGroup );

#############################################################################
##
#R  IsRcwaGroupsIteratorRep . . . . . . . . . . . . . iterator representation
##
DeclareRepresentation( "IsRcwaGroupsIteratorRep",
                       IsComponentObjectRep,
                       [ "G", "sphere", "oldsphere", "pos" ] );

#############################################################################
##
#S  RCWA(R) and CT(R). //////////////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#O  RCWACons( <R> ) . . . . . . . . . . . . . . . . . .  RCWA( R ) for ring R
#F  RCWA( <R> )
##
DeclareConstructor( "RCWACons", [ IsRcwaGroup, IsRing ] );
DeclareConstructor( "RCWACons", [ IsRcwaGroup, IsRowModule ] );
DeclareGlobalFunction( "RCWA" );

#############################################################################
##
#P  IsNaturalRCWA( <G> ) . . . . . . . . . . . . . . . . . . . . .  RCWA( R )
#P  IsNaturalRCWA_Z( <G> ) . . . . . . . . . . . . . . . . . . . .  RCWA( Z )
#P  IsNaturalRCWA_ZxZ( <G> ) . . . . . . . . . . . . . . . . . .  RCWA( Z^2 )
#P  IsNaturalRCWA_Z_pi( <G> )  . . . . . . . . . . . . . . . . RCWA( Z_(pi) )
#P  IsNaturalRCWA_GFqx( <G> )  . . . . . . . . . . . . . . . RCWA( GF(q)[x] )
##
DeclareCategory( "IsNaturalRCWA", IsRcwaGroup );
DeclareCategory( "IsNaturalRCWA_Z", IsRcwaGroup );
DeclareCategory( "IsNaturalRCWA_ZxZ", IsRcwaGroup );
DeclareCategory( "IsNaturalRCWA_Z_pi", IsRcwaGroup );
DeclareCategory( "IsNaturalRCWA_GFqx", IsRcwaGroup );

#############################################################################
##
#F  NrConjugacyClassesOfRCWAZOfOrder( <ord> ) . #Ccl of RCWA(Z) / order <ord>
#F  NrConjugacyClassesOfCTZOfOrder( <ord> ) . . . #Ccl of CT(Z) / order <ord>
##
##  Returns the number of conjugacy classes of the whole group RCWA(Z),
##  respectively CT(Z), of elements of order <ord>. The latter assumes the
##  conjecture that CT(Z) is the setwise stabilizer of N_0 in RCWA(Z).
##
DeclareGlobalFunction( "NrConjugacyClassesOfRCWAZOfOrder" );
DeclareGlobalFunction( "NrConjugacyClassesOfCTZOfOrder" );

#############################################################################
##
#A  Sign( <g> ) . . . . . . . . . . . .  sign of the element <g> of RCWA( Z )
##
##  The *sign* of the rcwa permutation <g>.
##  The sign mapping is an epimorphism from RCWA(Z) to U(Z) = <-1> = C_2.
##
DeclareAttribute( "Sign", IsRcwaMapping );

#############################################################################
##
#A  SignInOddCTPZ( <g> ) . . .  sign of <g> as element of CT_P(Z), 2 \notin P
##
##  The *sign* of the element <g> of CT_P(Z), where P does not contain 2.
##  This sign mapping is an epimorphism from CT_P(Z) to U(Z) = <-1> = C_2.
##  Since there is no such epimorphism if P contains 2, the prime set of <g>
##  must not contain 2.
##
DeclareAttribute( "SignInOddCTPZ", IsRcwaMappingOfZ );

#############################################################################
##
#O  CTCons( <R> ) . . . . . . . . . . . . . . . . . . . .  CT( R ) for ring R
#O  CTCons( <P>, <R> )  . . . . . . . . . . . . . . . . CT( P, R ) for ring R
#F  CT( <R> )
#F  CT( <P>, <R> )
##
DeclareConstructor( "CTCons", [ IsRcwaGroup, IsRing ] );
DeclareConstructor( "CTCons", [ IsRcwaGroup, IsList, IsRing ] );
DeclareConstructor( "CTCons", [ IsRcwaGroup, IsRowModule ] );
DeclareGlobalFunction( "CT" );

#############################################################################
##
#P  IsNaturalCT( <G> ) . . . . . . . . . . . . . . . . . . . . . . .  CT( R )
#P  IsNaturalCT_Z( <G> ) . . . . . . . . . . . . . . . . . . . . . .  CT( Z )
#P  IsNaturalCTP_Z( <G> )  . . . . . . . . . . . . . . . . . . . . CT( P, Z )
#P  IsNaturalCT_ZxZ( <G> ) . . . . . . . . . . . . . . . . . . . .  CT( Z^2 )
#P  IsNaturalCT_Z_pi( <G> )  . . . . . . . . . . . . . . . . . . CT( Z_(pi) )
#P  IsNaturalCT_GFqx( <G> )  . . . . . . . . . . . . . . . . . CT( GF(q)[x] )
##
DeclareCategory( "IsNaturalCT", IsRcwaGroup );
DeclareCategory( "IsNaturalCT_Z", IsRcwaGroup );
DeclareCategory( "IsNaturalCTP_Z", IsRcwaGroup );
DeclareCategory( "IsNaturalCT_ZxZ", IsRcwaGroup );
DeclareCategory( "IsNaturalCT_Z_pi", IsRcwaGroup );
DeclareCategory( "IsNaturalCT_GFqx", IsRcwaGroup );

#############################################################################
## 
#F  AllElementsOfCTZWithGivenModulus( m ) .  elements of CT(Z) with modulus m
##
##  Returns a list of all elements of CT(Z) with modulus m, under the
##  assumption of the conjecture that CT(Z) is the setwise stabilizer of the
##  nonnegative integers in RCWA(Z).
##
DeclareGlobalFunction( "AllElementsOfCTZWithGivenModulus" );

#############################################################################
## 
#A  DecompositionIntoPermutationalAndOrderPreservingElement( <g> )
##
DeclareAttribute( "DecompositionIntoPermutationalAndOrderPreservingElement",
                  IsRcwaMapping );
 
#############################################################################
##
#P  IsNaturalRCWA_OR_CT( <G> ) . . . . . . . . . . . . . RCWA( R ) or CT( R )
##
DeclareCategory( "IsNaturalRCWA_OR_CT", IsRcwaGroup );

#############################################################################
##
#S  Constructing rcwa groups. ///////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#O  IsomorphismRcwaGroup( <G>, <R> ) . .  rcwa representation of <G> over <R>
#O  IsomorphismRcwaGroup( <G>, <cl> )  . . rcwa representation of <G> on <cl>
#O  IsomorphismRcwaGroup( <G> )  . . . . .  rcwa representation of <G> over Z
#A  IsomorphismRcwaGroupOverZ( <G> ) . . . . . .  the corresponding attribute
##
##  Returns a faithful rcwa representation of the group <G> over
##  the ring <R>, respectively over Z.
##
DeclareOperation( "IsomorphismRcwaGroup", [ IsGroup, IsResidueClass ] );
DeclareOperation( "IsomorphismRcwaGroup", [ IsGroup ] );
DeclareAttribute( "IsomorphismRcwaGroupOverZ", IsGroup );

# every ring is a residue class in itself; several InstallMethod calls for
# IsomorphismRcwaGroup rely on this implication
InstallTrueMethod( IsResidueClass, IsRing );

#############################################################################
##
#O  Restriction( <g>, <f> ) . . . . . . . . . . . . restriction of <g> by <f>
#O  Restriction( <M>, <f> ) . . . . . . . . . . . . restriction of <M> by <f>
##
##  Returns the *restriction* of the rcwa mapping <g> resp. rcwa monoid <M>
##  by (i.e. to the image of) the rcwa mapping <f>. The mapping <f> must be
##  injective.
##
DeclareOperation( "Restriction", [ IsRcwaMapping, IsRcwaMapping ] );
DeclareOperation( "Restriction", [ IsRcwaMonoid, IsRcwaMapping ] );

#############################################################################
##
#O  Induction( <g>, <f> ) . . . . . . . . . . . . . . induction of <g> by <f>
#O  Induction( <M>, <f> ) . . . . . . . . . . . . . . induction of <M> by <f>
##
##  Returns the *induction* of the rcwa mapping <g> resp. the rcwa monoid <M>
##  by the rcwa mapping <f>.
##
##  The mapping <f> must be injective. In the first case, the support of <g>
##  and its images under powers of <g> must be subsets of the image of <f>.
##  In the second case, the support of <M> and its images under all elements
##  of <M> must be subsets of the image of <f>. If <M> is an rcwa group, the
##  latter simplifies to the condition that the support of <M> is a subset of
##  the image of <f>.
##
##  We have Induction( Restriction( <g>, <f> ), <f> ) = <g> as well as
##  Induction( Restriction( <M>, <f> ), <f> ) = <M>. Therefore induction is
##  the right inverse of restriction.
##
DeclareOperation( "Induction", [ IsRcwaMapping, IsRcwaMapping ] );
DeclareOperation( "Induction", [ IsRcwaMonoid, IsRcwaMapping ] );

#############################################################################
##
#O  Mirrored( <f> ) . .  conjugate of the rcwa mapping <f> under n |-> -n - 1
#O  Mirrored( <M> ) . .  conjugate of the rcwa monoid  <M> under n |-> -n - 1
##
##  The conjugate of an rcwa mapping <f> or an rcwa monoid <M> under the per-
##  mutation n |-> -n - 1 acts on the nonnegative integers as <f>, respec-
##  tively, <M> does on the negative integers, and vice versa.
##
DeclareOperation( "Mirrored", [ IsRcwaMappingOfZ ] );
DeclareOperation( "Mirrored", [ IsRcwaMonoidOverZ ] );

#############################################################################
##
#F  GroupByResidueClasses( <classes> ) . . . . . .  group permuting <classes>
##
##  Returns the group which is generated by all class transpositions which
##  interchange disjoint residue classes in <classes>.
##
##  The argument <classes> must be a list of residue classes.
##
##  Examples: If the residue classes in <classes> are pairwise disjoint, then
##            the returned group is the symmetric group on <classes>.
##            If every class in <classes> has nontrivial intersection with
##            every other class, then the returned group is trivial.
##
##  In many cases, the returned group is infinite.
##
DeclareGlobalFunction( "GroupByResidueClasses" );

#############################################################################
##
#O  MergerExtension( <G>, <points>, <point> )
##
##  Thinking of the moved points of the finite permutation group <G> being
##  infinite sets themselves, this operation returns a group isomorphic
##  to <G,g>, where g is an involution which interchanges the union of the
##  points in <points> and the point <point>.
##
##  The arguments are a finite permutation group <G>, a set <points> of
##  points moved by <G> and a single point <point> moved by <G> which is not
##  in <points>.
##
DeclareOperation( "MergerExtension", [ IsPermGroup, IsList, IsPosInt ] );

#############################################################################
##
#S  The action of an rcwa group on the underlying ring. /////////////////////
##
#############################################################################

#############################################################################
##
#C  IsRcwaGroupOrbit . . . category of orbits under the action of rcwa groups
##
##  The category of all orbits under the action of rcwa groups which are
##  neither represented as lists nor as residue class unions.
##
DeclareCategory( "IsRcwaGroupOrbit", IsListOrCollection );

#############################################################################
##
#A  UnderlyingGroup( <orbit> ) . . . . . . . . . underlying group of an orbit
##
DeclareAttribute( "UnderlyingGroup", IsRcwaGroupOrbit );

#############################################################################
##
#R  IsRcwaGroupOrbitStandardRep . . . . . "standard" representation of orbits
##
DeclareRepresentation( "IsRcwaGroupOrbitStandardRep",
                       IsComponentObjectRep and IsAttributeStoringRep,
                       [ "group", "representative", "action" ] );

#############################################################################
##
#R  IsRcwaGroupOrbitsIteratorRep . .  repr. of iterators of rcwa group orbits
##
DeclareRepresentation( "IsRcwaGroupOrbitsIteratorRep",
                       IsComponentObjectRep,
                       [ "orbit", "sphere", "oldsphere", "pos" ] );

#############################################################################
##
#O  GrowthFunctionOfOrbit( <G>, <n>, <r_max>, <size_max> )
#O  GrowthFunctionOfOrbit( <orbit>, <r_max>, <size_max> )
##
##  Returns a list whose (r+1)-th entry is the size of the sphere of radius r
##  about <n> under the action of the group <G>.
##
##  The argument <r_max> is the largest possible radius to be considered,
##  and the computation stops once the sphere size exceeds <size_max>.
##
##  In place of the arguments <G> and <n>, one can also supply an orbit
##  object.
##
DeclareOperation( "GrowthFunctionOfOrbit",
                  [ IsGroup, IsObject, IsPosInt, IsPosInt ] );
DeclareOperation( "GrowthFunctionOfOrbit",
                  [ IsListOrCollection, IsPosInt, IsPosInt ] );

#############################################################################
##
#O  CyclesOnFiniteOrbit( <G>, <g>, <n> ) . . . cycles of <g> on orbit <n>^<G>
##
##  Returns a list of all cycles of the rcwa permutation <g> on the orbit
##  of the point <n> under the action of the rcwa group <G>. It is assumed
##  that <g> is an element of <G>, and that the orbit of <n> under the action
##  of <G> is finite. These conditions are not checked.
##
DeclareOperation( "CyclesOnFiniteOrbit",
                  [ IsRcwaGroup, IsRcwaMapping, IsObject ] );

#############################################################################
##
#O  GuessOrbitRepresentatives( <G>, <bound_or_range>, <search_bound> )
##
##  Returns a tentative list of orbit representatives.
##  The meaning of the arguments depends on the method.
##
DeclareOperation( "GuessOrbitRepresentatives",
                  [ IsRcwaGroup, IsObject, IsObject ] );

#############################################################################
##
#O  IsTransitive( <G>, <S> ) . . . . . . . . . . . . . . . .  for rcwa groups
#O  Transitivity( <G>, <S> )
#O  IsPrimitive( <G>, <S> )
##
DeclareOperation( "IsTransitive", [ IsRcwaGroup, IsListOrCollection ] );
DeclareOperation( "Transitivity", [ IsRcwaGroup, IsListOrCollection ] );
DeclareOperation( "IsPrimitive",  [ IsRcwaGroup, IsListOrCollection ] );

#############################################################################
##
#P  IsTransitiveOnNonnegativeIntegersInSupport( <G> )
##
##  Returns true or false, depending on whether the action of the rcwa group
##  G < RCWA(Z) on the set of its nonnegative moved points is transitive.
##  As such transitivity test is a computationally hard problem, methods may
##  fail or run into an infinite loop.
##
DeclareProperty( "IsTransitiveOnNonnegativeIntegersInSupport",
                 IsRcwaGroupOverZ );

#############################################################################
##
#O  TryIsTransitiveOnNonnegativeIntegersInSupport( <G>, <searchlimit> )
##
##  This operation tries to figure out whether the action of the group
##  G < RCWA(Z) on the set of its nonnegative moved points is transitive.
##  It returns a string briefly describing the situation. If the determina-
##  tion of transitivity is successful, the property `IsTransitiveOnNonnega-
##  tiveIntegersInSupport' is set accordingly. The argument <searchlimit>
##  is a bound on the efforts to be made -- more precisely, this is the
##  maximum search radius for a smaller point in a sphere about a point.
##  
DeclareOperation( "TryIsTransitiveOnNonnegativeIntegersInSupport",
                  [ IsRcwaGroupOverZ, IsPosInt ] );

#############################################################################
##
#A  TransitivityCertificate( <G> )
##
##  Given an rcwa group <G> over Z which acts transitively on the set of
##  nonnegative integers in its support, this attribute is a record
##  containing components 'phi', 'words' and 'classes' as follows:
##
##  - 'phi' is an epimorphism from a free group to <G> which maps generators
##    to generators.
##
##  - 'words' is a list, where words[i] is a preimage under phi of an element
##    of <G> which maps all sufficiently large positive integers in the
##    residue classes classes[i] to smaller integers.
##
##  There are no methods installed for `TransitivityCertificate' -- attribute
##  values are computed with `TryToComputeTransitivityCertificate'.
##
DeclareAttribute( "TransitivityCertificate", IsRcwaGroup );

#############################################################################
##
#O  TryToComputeTransitivityCertificate( <G>, <searchlimit> )
#O  SimplifiedCertificate( <cert> )
##
##  The operation `TryToComputeTransitivityCertificate' tries to compute a
##  "transitivity certificate" as described above for the action of the rcwa
##  group <G> over Z on the set of nonnegative integers in its support. Of
##  course this can be successful only if this action is indeed transitive.
##  The argument <searchlimit> is the largest radius of a ball about a point
##  within which smaller points are looked for and taken into consideration.
##  The computed certificate is returned.
##  
##  The operation `SimplifiedCertificate' tries to simplify the transitivity
##  certificate <cert> by removing redundant words.
##  The simplified certificate is returned.
##
DeclareOperation( "TryToComputeTransitivityCertificate",
                  [ IsRcwaGroup, IsPosInt ] );
DeclareOperation( "SimplifiedCertificate", [ IsRecord ] );

#############################################################################
##
#O  TryToComputeDegreeOfTransitivity( <G>, <timelimit> )
##
##  Tries to determine the degree of transirivity of the action of the group
##  <G> on its support, and -- after approximately <timelimit> milliseconds
##  have passed -- returns part of a stabilizer chain. Information on the
##  progress of the computation is printed to the screen.
##  
DeclareOperation( "TryToComputeDegreeOfTransitivity",
                  [ IsRcwaGroup, IsPosInt ] );

#############################################################################
##
#O  SupersetOfOrbitRepresentatives( <G>, <maxsaddle>, <maxprog> )
##
##  Returns a record with the following components:
##
##   - R: A set which has nontrivial intersection with every orbit of the
##        subgroup <G> of CT(Z) on the nonnegative integers.
##        The parameters <maxsaddle> and <maxprog> can be used to control
##        the size of this set. In general, larger values may make the set
##        smaller.
##
##   - D: A list of residue class unions whose union is a (not necessarily
##        proper) superset the complement of R in Z. The intersection of R
##        and the union of the sets in D is always finite.
##
##   - g: A list of elements of <G> such that n^g[i] < n for all sufficiently
##        large n in D[i], for i = 1, ... , Length(g) = Length(D).
##
##   - phi: An epimorphism from a free group F of rank the number of
##          generators of <G> to <G> which maps generators to generators.
##
##   - w: A list of words w[i] in F such that w[i]^phi = g[i],
##        for i = 1, ... , Length(w) = Length(g).
##
DeclareOperation( "SupersetOfOrbitRepresentatives",
                  [ IsRcwaGroup, IsRingElement, IsRingElement ] );

#############################################################################
##
#O  DistanceToNextSmallerPointInOrbit( <G>, <n> )
##
##  Returns the smallest number d such that there is a product g of d genera-
##  tors or inverses of generators of <G> which maps <n> to an integer with
##  absolute value less than |<n>|.
##
DeclareOperation( "DistanceToNextSmallerPointInOrbit", [ IsGroup, IsInt ] );

#############################################################################
##
#O  ShortResidueClassOrbits( <G>, <modulusbound>, <maxlng> )
##
##  Returns a list of all orbits of residue classes of the rcwa group <G>
##  which contain a residue class r(m) such that m divides <modulusbound>,
##  and which are not longer than <maxlng>.
##
DeclareOperation( "ShortResidueClassOrbits", [ IsRcwaGroup, IsRingElement,
                                               IsPosInt ] );

#############################################################################
##
#O  StabilizerOp( <G>, <n> ) . . . . . . .  point stabilizer in an rcwa group
#O  StabilizerOp( <G>, <S>, <action> ) . . .  set stabilizer in an rcwa group
#A  StabilizerInfo( <G> ) . .  info. on what is stabilized under which action
##
DeclareOperation( "StabilizerOp", [ IsRcwaGroup, IsRingElement ] );
DeclareOperation( "StabilizerOp", [ IsRcwaGroup, IsListOrCollection ] );
DeclareOperation( "StabilizerOp", [ IsRcwaGroup, IsListOrCollection,
                                    IsFunction ] );
DeclareAttribute( "StabilizerInfo", IsRcwaGroup );

#############################################################################
##
#O  RepresentativeActionOp( <G>, <src>, <dest>, <act> )
##
DeclareOperation( "RepresentativeActionOp",
                  [ IsGroup, IsObject, IsObject, IsFunction ] );

#############################################################################
##
#O  RepresentativeActionPreImage( <G>, <src>, <dest>, <act>, <F> )
#O  RepresentativesActionPreImage( <G>, <src>, <dest>, <act>, <F> )
##
##  Returns a preimage, respectively a list of preimages, of an element of
##  <G> which maps <src> to <dest> under the natural projection from the
##  free group <F> onto <G>. The rank of <F> must be equal to the number of
##  generators of <G>. Often, finding several representatives of the preimage
##  is not harder than computing just one.
##
DeclareOperation( "RepresentativeActionPreImage",
                  [ IsGroup, IsObject, IsObject, IsFunction, IsFreeGroup ] );
DeclareOperation( "RepresentativesActionPreImage",
                  [ IsGroup, IsObject, IsObject, IsFunction, IsFreeGroup ] );

#############################################################################
##
#O  OrbitUnion( <G>, <S> ) . . . . . . .  union of the orbit of <S> under <G>
##
##  Returns the union of the elements of the orbit of the set <S> under the
##  rcwa group <G>. In particular, <S> can be a union of residue classes.
##
DeclareOperation( "OrbitUnion", [ IsRcwaGroup, IsListOrCollection ] );

#############################################################################
##
#O  ProjectionsToInvariantUnionsOfResidueClasses( <G>, <m> )
##
##  Projections of the rcwa group <G> to unions of residue classes (mod m)
##  which it fixes setwise.
##
DeclareOperation( "ProjectionsToInvariantUnionsOfResidueClasses",
                  [ IsRcwaGroup, IsRingElement ] );

#############################################################################
##
#O  CollatzLikeMappingByOrbitTree( <G>, <root>, <min_r>, <max_r> )
##
##  This operation is so far undocumented since its meaning has yet to be
##  settled.
##
DeclareOperation( "CollatzLikeMappingByOrbitTree",
                  [ IsRcwaGroup, IsRingElement, IsPosInt, IsPosInt ] );

#############################################################################
##
#F  DrawOrbitPicture( <G>, <p0>, <r>, <height>, <width>, <colored>,
#F                    <palette>, <filename> )
##
##  Draws a picture of the orbit(s) of the point(s) <p0> under the action of
##  the group <G> on Z^2.
##
##  The argument <p0> is either one point or a list of points. The argument
##  <r> denotes the radius of the ball around <p0> to be computed. The size
##  of the created picture is <height>x<width> pixels. The argument <colored>
##  is a boolean which specifies whether a 24-bit True Color picture or a
##  monochrome picture should be created. In the former case, <palette> must
##  be a list of triples of integers in the range 0..255, denoting the RGB
##  values of colors to be used. In the latter case, the argument <palette>
##  is not used, and any value can be passed.
##
##  The resulting picture is written in bitmap- (bmp-) format to a file named
##  <filename>. The filename should include the entire pathname.
##
DeclareGlobalFunction( "DrawOrbitPicture" );

#############################################################################
##
#S  Tame rcwa groups and respected partitions. //////////////////////////////
##
#############################################################################

#############################################################################
##
#A  RespectedPartition( <G> ) . . . . . . . . . . . . . . respected partition
#A  RespectedPartition( <sigma> )
##
##  A partition of the base ring R into a finite number of residue classes
##  on which the rcwa group <G> acts as a permutation group, and on whose
##  elements all elements of <G> are affine. Provided that R has a residue
##  class ring of cardinality 2, such a partition exists if and only if <G>
##  is tame. The respected partition of a bijective rcwa mapping <sigma> is
##  defined as the respected partition of the cyclic group generated by
##  <sigma>.
##
DeclareAttribute( "RespectedPartition", IsRcwaGroup );
DeclareAttribute( "RespectedPartition", IsRcwaMapping );

#############################################################################
##
#O  RespectsPartition( <G>, <P> )
#O  RespectsPartition( <sigma>, <P> )
##
##  Checks whether the rcwa group <G> resp. the rcwa permutation <sigma>
##  respects the partition <P>.
##
DeclareOperation( "RespectsPartition", [ IsObject, IsList ] );

#############################################################################
##
#A  ActionOnRespectedPartition( <G> ) .  action of <G> on respected partition
##
##  The action of the tame group <G> on its stored respected partition.
##
DeclareAttribute( "ActionOnRespectedPartition", IsRcwaGroup );

#############################################################################
##
#A  KernelOfActionOnRespectedPartition( <G> )
#A  RankOfKernelOfActionOnRespectedPartition( <G> )
##
##  The kernel of the action of <G> on the stored respected partition,
##  resp. the rank of the largest free abelian group fitting into it. 
##  The group <G> must be tame.
##
DeclareAttribute( "KernelOfActionOnRespectedPartition", IsRcwaGroup );
DeclareAttribute( "RankOfKernelOfActionOnRespectedPartition", IsRcwaGroup );

#############################################################################
##
#A  RefinedRespectedPartitions( <G> )
#A  KernelActionIndices( <G> )
##
##  Refinements of the stored respected partition P of <G>, resp. the orders
##  of the permutation groups induced by the kernel of the action of <G> on P
##  on these refinements.
##
DeclareAttribute( "RefinedRespectedPartitions", IsRcwaGroup );
DeclareAttribute( "KernelActionIndices", IsRcwaGroup );

#############################################################################
##
#A  IsomorphismMatrixGroup( <G> ) . . . . . . .  matrix representation of <G>
##
##  A linear representation of the rcwa group <G> over the quotient field of
##  its underlying ring.
##
##  Tame rcwa groups have linear representations over the quotient field of
##  their underlying ring. There is such a representation whose degree is
##  twice the length of a respected partition.
##
DeclareAttribute( "IsomorphismMatrixGroup", IsGroup );

#############################################################################
##
#A  IntegralConjugate( <g> ) . . . . . . . . . . .  integral conjugate of <g>
#A  IntegralConjugate( <G> ) . . . . . . . . . . .  integral conjugate of <G>
#A  IntegralizingConjugator( <g> ) . . . . . . . mapping x: <g>^x is integral
#A  IntegralizingConjugator( <G> ) . . . . . . . mapping x: <G>^x is integral
##
##  Some integral conjugate of the rcwa mapping <g> resp. rcwa group <G>
##  in RCWA(R).
##
##  Such a conjugate exists always if <g> is a tame bijective rcwa mapping
##  respectively if <G> is a tame rcwa group, and if the underlying ring R
##  has residue class rings of any finite cardinality. Integral conjugates
##  are of course not unique.
##
DeclareAttribute( "IntegralConjugate", IsRcwaMapping );
DeclareAttribute( "IntegralConjugate", IsRcwaGroup );
DeclareAttribute( "IntegralizingConjugator", IsRcwaMapping );
DeclareAttribute( "IntegralizingConjugator", IsRcwaGroup );

#############################################################################
##
#A  StandardConjugate( <g> ) . .  standard rep. of the conjugacy class of <g>
#A  StandardConjugate( <G> ) . .  standard rep. of the conjugacy class of <G>
#A  StandardizingConjugator( <g> ) . . . . . . . mapping x: <g>^x is standard
#A  StandardizingConjugator( <G> ) . . . . . . . mapping x: <G>^x is standard
##
##  The "standard conjugate" is some "nice" canonical representative of the
##  conjugacy class of RCWA(R) which the bijective rcwa mapping <g> resp. the
##  rcwa group <G> belongs to. Two rcwa mappings / rcwa groups are conjugate
##  in RCWA(R) if and only if their "standard conjugates" are the same. Such
##  standard class representatives are currently only defined in rare cases.
##
DeclareAttribute( "StandardConjugate", IsRcwaMapping );
DeclareAttribute( "StandardConjugate", IsRcwaGroup );
DeclareAttribute( "StandardizingConjugator", IsRcwaMapping );
DeclareAttribute( "StandardizingConjugator", IsRcwaGroup );

#############################################################################
##
#O  CompatibleConjugate( <g>, <h> ) . . . . . . . . . .  compatible conjugate
##
##  Returns an rcwa permutation <h>^r such that there is a partition which is
##  respected by both <g> and <h>^r, hence such that the group generated by
##  <g> and <h>^r is tame. Methods may choose any such mapping.
##
DeclareOperation( "CompatibleConjugate", [ IsRcwaMapping, IsRcwaMapping ] );

#############################################################################
##
#F  CommonRefinementOfPartitionsOfR_NC( <partitions> ) . . . . . general case
#F  CommonRefinementOfPartitionsOfZ_NC( <partitions> ) . . special case R = Z
##
##  Returns the coarsest common refinement of the list <partitions> of
##  partitions of Z, respectively a ring R, into unions of residue classes.
##  Here the term "common refinement" means that each set in the returned
##  partition is a subset of exactly one set in each of the partitions in
##  <partitions>. The ring R may be any base ring supported by RCWA.
##  For R = Z the last-mentioned function is more efficient.
##
DeclareGlobalFunction( "CommonRefinementOfPartitionsOfR_NC" );
DeclareGlobalFunction( "CommonRefinementOfPartitionsOfZ_NC" );

#############################################################################
##
#O  RefinementSequence( <G>, <maxlng>, <maxparts> )
##
##  Returns a sequence P of partitions of the base ring of <G> as follows:
##
##  - P[1] is the return value of `CommonRefinementOfPartitionsOfR_NC' when
##    called for the list of respected partitions of the generators of <G>.
##
##  - For k > 1, P[k] is what `CommonRefinementOfPartitionsOfR_NC' returns
##    when called for the list of images of P[k-1] under the generators of
##    <G> (plus the identity).
##
##  The sequence is returned once its length reaches <maxlng> or the length
##  of a partition exceeds <maxparts>.
##
DeclareOperation( "RefinementSequence",
                  [ IsRcwaGroup, IsPosInt, IsPosInt ] );

#############################################################################
##
#P  IsNaturalRcwaRepresentationOfGLOrSL
##
DeclareCategory( "IsNaturalRcwaRepresentationOfGLOrSL",
                  IsGroupHomomorphism and IsBijective );

#############################################################################
##
#S  Words, free groups and fp groups. ///////////////////////////////////////
##
#############################################################################

#############################################################################
##
#O  EpimorphismsUpToAutomorphisms( G, H )
##
##  Epimorphisms from <G> to <H>, up to automorphisms of <H>.
##
DeclareOperation( "EpimorphismsUpToAutomorphisms", [ IsGroup, IsGroup ] );

#############################################################################
##
#F  ReducedWordByOrdersOfGenerators( <w>, <gensords> )
##
##  Given a word <w>, this function returns the word obtained from <w> by
##  reducing the exponents of powers of generators modulo their orders, as
##  specified in the list <gensords>.
##
DeclareGlobalFunction( "ReducedWordByOrdersOfGenerators" );

#############################################################################
##
#O  NormalizedRelator( <w>, <gensords> )
##
##  Given a word <w>, this operation returns its normal form obtained by
##
##    1. reducing the exponents of powers of generators modulo their orders,
##       as specified in the list <gensords>,
##    2. cyclic reduction and
##    3. cyclic conjugation to the lexicographically smallest such conjugate.
##
##  As the name of the operation suggests, the main purpose of this operation
##  is to get the relators in a finite presentation short and nice, and to be
##  able to spot and remove redundant relators in easy cases.
##
DeclareOperation( "NormalizedRelator", [ IsAssocWord, IsList ] );

#############################################################################
##
#A  RankOfFreeGroup( <Fn> )
##
DeclareAttribute( "RankOfFreeGroup", IsRcwaGroup );

#############################################################################
##
#O  EpimorphismFromFpGroup( <G>, <r> ) . .  epimorphism from an fp group to G
#O  EpimorphismFromFpGroup( <G>, <r>, <maxparts> )
##
##  Returns an epimorphism from a finitely presented group to the group <G>
##  The argument <r> denotes the radius of the ball around 1 which should be
##  searched for relations. If the optional argument <maxparts> is given, it
##  limits the search space to elements with at most <maxparts> affine parts.
##
DeclareOperation( "EpimorphismFromFpGroup",
                  [ IsFinitelyGeneratedGroup, IsPosInt ] );
DeclareOperation( "EpimorphismFromFpGroup",
                  [ IsFinitelyGeneratedGroup, IsPosInt, IsPosInt ] );

#############################################################################
##
#O  PreImagesRepresentatives( <map>, <elm> ) . . . .  several representatives
##
##  This is an analogue to `PreImagesRepresentative', which returns a list
##  of possibly several representatives if computing these is not harder than
##  computing just one representative.
##
DeclareOperation( "PreImagesRepresentatives",
                  [ IsGeneralMapping, IsObject ] );

#############################################################################
##
#S  Data libraries. /////////////////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#F  LoadRCWAExamples( ) . . . . . . . . . . . . . . .  load examples database 
##
##  This function loads RCWA's collection of examples.
##  It returns a record containing the individual examples as components.
##
DeclareGlobalFunction( "LoadRCWAExamples" );
DeclareSynonym( "RCWALoadExamples", LoadRCWAExamples );

#############################################################################
##
#F  LoadDatabaseOfProductsOf2ClassTranspositions( )
##
##  This function loads the data library of products of 2 class transposi-
##  tions which interchange residue classes with moduli <= 6.
##  It returns a record containing all data in the library.
##
DeclareGlobalFunction( "LoadDatabaseOfProductsOf2ClassTranspositions" );

#############################################################################
##
#F  LoadDatabaseOfNonbalancedProductsOfClassTranspositions( )
##
##  This function loads the data library of nonbalanced products of class
##  transpositions. It returns a record containing all data in the library.
##  Note that name and contents of this library will likely be changed in
##  the future.
##
DeclareGlobalFunction(
  "LoadDatabaseOfNonbalancedProductsOfClassTranspositions" );

#############################################################################
##
#F  LoadDatabaseOfGroupsGeneratedBy3ClassTranspositions( )
##
##  This function loads the data library of groups generated by 3 class
##  transpositions which interchange residue classes with moduli <= 6.
##  It returns a record containing all data in the library.
##
DeclareGlobalFunction(
  "LoadDatabaseOfGroupsGeneratedBy3ClassTranspositions" );

#############################################################################
##
#F  LoadDatabaseOfGroupsGeneratedBy4ClassTranspositions( )
##
##  This function loads the data library of groups generated by 4 class
##  transpositions which interchange residue classes with moduli <= 6.
##  It returns a record containing all data in the library.
##
DeclareGlobalFunction(
  "LoadDatabaseOfGroupsGeneratedBy4ClassTranspositions" );

#############################################################################
##
#F  LoadDatabaseOfCTGraphs( )
##
##  This function loads the database of realizations of finite graphs as
##  'class transposition graphs' -- the vertices are class transpositions,
##  and there is an edge connecting two vertices iff their product has finite
##  order, or equivalently, iff both vertices respect a common partition.
##
DeclareGlobalFunction( "LoadDatabaseOfCTGraphs" );

#############################################################################
##
#E  rcwagrp.gd . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
