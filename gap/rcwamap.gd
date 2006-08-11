#############################################################################
##
#W  rcwamap.gd                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains declarations of functions, operations etc. for
##  computing with rcwa mappings.
##
##  Let R be an infinite euclidean domain which is not a field and all of
##  whose proper residue class rings are finite. We call a mapping f: R -> R
##  *residue class-wise affine*, or in short an *rcwa* mapping, if there is
##  a nonzero m in R such that f is affine on residue classes (mod m).
##      This means that for any residue class r(m) in R/mR there are
##  coefficients a_r(m), b_r(m), c_r(m) in R such that the restriction of f
##  to the set r(m) = { r + km | k in R } is given by
##  
##                  n  |->  (a_r(m) * n + b_r(m))/c_r(m).
##  
##  We always assume that c_r(m) > 0, that all fractions are reduced,
##  i.e. that gcd( a_r(m), b_r(m), c_r(m) ) = 1, and that m is chosen
##  multiplicatively minimal.
##      Apart from the restrictions imposed by the condition that the image
##  of any residue class r(m) under f must be a subset of R and that one
##  cannot divide by 0, the coefficients a_r(m), b_r(m) and c_r(m) can be any
##  ring elements.
##      We call m the *modulus* of f. By *products* of rcwa mappings we
##  always mean their compositions as mappings, and by the *inverse* of
##  a bijective rcwa mapping we mean its inverse mapping. 
##      The set RCWA(R) := { g in Sym(R) | g is residue class-wise affine }
##  is closed under multiplication and taking inverses (this can be verified
##  easily), hence forms a subgroup of Sym(R).
##      While computing with permutations of infinite sets in general is
##  a very difficult task, the rcwa mappings form a class of permutations
##  which is accessible to computations.
##
##  In order to enter an rcwa mapping we need to specify the following:
##
##  - Underlying Ring: The underlying ring R is stored as the
##                     `UnderlyingRing' of the family the rcwa mapping object
##                     belongs to, and as value of the attribute `Source'.
##
##  - Modulus:         The modulus m is stored as a component <modulus> in
##                     any rcwa mapping object. 
##
##  - Coefficients:    The list of coefficients is stored as a component
##                     <coeffs> in any rcwa mapping object. The component
##                     <coeffs> is a list of |R/mR| lists of three elements
##                     of R, each, giving the coefficients a_r(m), b_r(m)
##                     and c_r(m) for r(m) running through all residue
##                     classes (mod m). The ordering of these triples is
##                     defined by the ordering of the residues r mod m
##                     in `AllResidues( <R>, <m> )'.
##
##  It is always taken care that the entries of the stored coefficient
##  triples of an rcwa mapping are coprime, that the third entry of any
##  coefficient triple equals its standard conjugate and that the number of
##  stored coefficient triples equals the number of residue classes modulo
##  the modulus of the mapping. Given this, an rcwa mapping determines its
##  internal representation uniquely. Thus testing rcwa mappings for equality
##  is very cheap. The above also prevents unnecessary coefficient explosion.
##
Revision.rcwamap_gd :=
  "@(#)$Id$";

#############################################################################
##
#V  InfoRCWA . . . . . . . . . . . . . . . . . .  info class for RCWA package
##
##  This is the Info class of the RCWA package.
##
##  See Section "Info Functions" in the GAP Reference Manual for
##  a description of the Info mechanism.
##
DeclareInfoClass( "InfoRCWA" );

#############################################################################
##
#F  RCWAInfo . . . . . . . . . . . . . . . . . . set info level of `RcwaInfo'
##
##  For convenience: `RCWAInfo( <n> )' is a shorthand for
##  `SetInfoLevel( RcwaInfo, <n> )'.
##
DeclareGlobalFunction( "RCWAInfo" );

#############################################################################
##
#C  IsRcwaMapping . . . . . . . . . . . . . . . . . . . . . all rcwa mappings
##
##  The category of all rcwa mappings.
##
DeclareCategory( "IsRcwaMapping", IsRingElement );

#############################################################################
##
#C  IsRcwaGroup . . . . . . . . . . . . . . . . . . . . . . . all rcwa groups
##
##  The category of all rcwa groups.
##
DeclareSynonym( "IsRcwaGroup",
                 CategoryCollections(IsRcwaMapping) and IsGroup );

#############################################################################
##
#C  IsRcwaMappingOfZ . . . . . . . . . . . . . . . . . . . rcwa mappings of Z
##
##  The category of all rcwa mappings of Z.
##
DeclareCategory( "IsRcwaMappingOfZ", IsRingElement );

#############################################################################
##
#C  IsRcwaMappingOfZ_pi . . . . . . . . . . . . . . . rcwa mappings of Z_(pi)
##
##  The category of all rcwa mappings of semilocalizations of Z.
##
DeclareCategory( "IsRcwaMappingOfZ_pi", IsRingElement );

#############################################################################
##
#C  IsRcwaMappingOfZOrZ_pi . . . . . . . . . . . rcwa mappings of Z or Z_(pi)
##
##  The category of all rcwa mappings of the ring Z or semilocalizations
##  thereof. This is the union of the categories `IsRcwaMappingOfZ' and
##  `IsRcwaMappingOfZ_pi'.
##
DeclareCategory( "IsRcwaMappingOfZOrZ_pi", IsRingElement );

#############################################################################
##
#C  IsRcwaMappingOfGFqx . . . . . . . . . . . . . . rcwa mappings of GF(q)[x]
##
##  The category of all rcwa mappings of polynomial rings in one variable
##  over finite fields.
##
DeclareCategory( "IsRcwaMappingOfGFqx", IsRingElement );

#############################################################################
##
#A  UnderlyingField( <f> ) . . . . . . coefficient field of the source of <f>
##
DeclareAttribute( "UnderlyingField", IsRcwaMappingOfGFqx );

#############################################################################
##
#F  RcwaMappingsFamily( <R> ) . . . family of rcwa mappings over the ring <R>
##
DeclareGlobalFunction( "RcwaMappingsFamily" );

#############################################################################
##
#F  RcwaMappingsOfZ_piFamily( <primes> )
##
##  Family of rcwa mappings with underlying ring Z_(pi), where the set pi
##  is given as a list <primes>.
##
DeclareGlobalFunction( "RcwaMappingsOfZ_piFamily" );

#############################################################################
##
#F  RcwaMappingsOfGFqxFamily( <R> ) . family of rcwa mappings of R = GF(q)[x]
##
##  Family of rcwa mappings of R = GF(q)[x].
##
DeclareGlobalFunction( "RcwaMappingsOfGFqxFamily" );

#############################################################################
##
#R  IsRcwaMappingStandardRep . . . "standard" representation of rcwa mappings
##
##  Representation of rcwa mappings by modulus <modulus> (in the following
##  denoted by m) and coefficient list <coeffs>.
##
##  The component <coeffs> is a list of |R/mR| lists of three elements of
##  the underlying ring R, each, giving the coefficients a_r(m), b_r(m) and
##  c_r(m) for r(m) running through all residue classes (mod m).
##
##  The ordering of these triples is defined by the ordering of the residues
##  r mod m in the return value of `AllResidues( <R>, <m> )'.
##
DeclareRepresentation( "IsRcwaMappingStandardRep",
                       IsComponentObjectRep and IsAttributeStoringRep,
                       [ "modulus", "coeffs" ] );

#############################################################################
##
#M  RcwaMapping( <R>, <m>, <coeffs> )
#M  RcwaMapping( <R>, <coeffs> )
#M  RcwaMapping( <coeffs> )
#M  RcwaMapping( <perm>, <range> )
#M  RcwaMapping( <m>, <values> )
#M  RcwaMapping( <pi>, <coeffs> )
#M  RcwaMapping( <q>, <m>, <coeffs> )
#M  RcwaMapping( P1, P2 )
#M  RcwaMapping( <cycles> )
#M  RcwaMappingNC( <R>, <m>, <coeffs> )
#M  RcwaMappingNC( <R>, <coeffs> )
#M  RcwaMappingNC( <coeffs> )
#M  RcwaMappingNC( <perm>, <range> )
#M  RcwaMappingNC( <m>, <values> )
#M  RcwaMappingNC( <pi>, <coeffs> )
#M  RcwaMappingNC( <q>, <m>, <coeffs> )
#M  RcwaMappingNC( P1, P2 )
#M  RcwaMappingNC( <cycles> )
##
##  Construction of the rcwa mapping 
##
##  (a) of <R> with modulus <m> and coefficients <coeffs>, resp.
##
##  (b) of <R> = Z or <R> = Z_(pi) with modulus Length( <coeffs> )
##      and coefficients <coeffs>, resp.
##
##  (c) of R = Z with modulus Length( <coeffs> ) and coefficients
##      <coeffs>, resp.
##
##  (d)  of R = Z, acting on any set <range> + k * Length(<range>) like the
##       permutation <perm> on <range>, resp.
##
##  (e) of R = Z with modulus <m> and values prescribed by the
##      list <values>, which consists of 2 * <m> pairs giving preimage
##      and image for 2 points per residue class (mod <m>) resp.
##
##  (f) of R = Z_(pi) with with modulus Length( <coeffs> ) and coefficients
##      <coeffs>, resp.
##
##  (g) of GF(q)[x] with modulus <m> and coefficients <coeffs>, resp.
##
##  (h) a bijective rcwa mapping which induces a bijection between the
##      partitions <P1> and <P2> of R into residue classes and which is
##      affine on the elements of <P1>, resp.
##
##  (i) a bijective rcwa mapping with "residue  class cycles" as given by
##      <cycles>.  The latter is a list of lists of pairwise disjoint residue
##      classes which the mapping should permute cyclically, each.
##
##  The difference between `RcwaMapping' and `RcwaMappingNC' is that the
##  former performs some argument checks which are omitted in the latter,
##  where just anything may happen if wrong or inconsistent arguments
##  are given.
##
DeclareOperation( "RcwaMapping", [ IsObject ] );
DeclareOperation( "RcwaMapping", [ IsObject, IsObject ] );
DeclareOperation( "RcwaMapping", [ IsObject, IsObject, IsObject ] );
DeclareOperation( "RcwaMappingNC", [ IsObject ] );
DeclareOperation( "RcwaMappingNC", [ IsObject, IsObject ] );
DeclareOperation( "RcwaMappingNC", [ IsObject, IsObject, IsObject ] );

#############################################################################
##
#O  Modulus( <f> ) . . . . . . . . . . .  the modulus of the rcwa mapping <f>
#O  Modulus( <G> ) . . . . . . . . . . .  the modulus of the rcwa group <G>
##
##  See also the attribute `ModulusOfRcwaGroup'.
##
DeclareOperation( "Modulus", [ IsRcwaMapping ] );
DeclareOperation( "Modulus", [ IsRcwaGroup ] );

#############################################################################
##
#O  Coefficients( <f> ) . . . . . .  the coefficients of the rcwa mapping <f>
##
DeclareOperation( "Coefficients", [ IsRcwaMapping ] );

#############################################################################
##
#F  LocalizedRcwaMapping( <f>, <p> )
#F  SemilocalizedRcwaMapping( <f>, <pi> )
##
##  These functions return the rcwa mapping of Z_(p) resp. Z_(pi) with the
##  same coefficients as <f>.
##
DeclareGlobalFunction( "LocalizedRcwaMapping" );
DeclareGlobalFunction( "SemilocalizedRcwaMapping" );

#############################################################################
##
#A  Multiplier( <f> ) . . . . . . . .  the multiplier of the rcwa mapping <f>
##
##  We define the *multiplier* of an rcwa mapping <f> by the standard
##  associate of the least common multiple of the coefficients a_r(m).
##
##  We define the *multiplier* of an rcwa group by the lcm of the multipliers
##  of its elements, if such an lcm exists, and by infinity otherwise.
##
DeclareAttribute( "Multiplier", IsRcwaMapping );
DeclareAttribute( "Multiplier", IsRcwaGroup );
DeclareSynonym( "Mult", Multiplier );

#############################################################################
##
#A  Divisor( <f> ) . . . . . . . . . . .  the divisor of the rcwa mapping <f>
##
##  We define the *divisor* of an rcwa mapping <f> by the standard
##  associate of the least common multiple of the coefficients c_r(m).
##
##  We define the *divisor* of an rcwa group by the lcm of the divisors of
##  its elements, if such an lcm exists, and by infinity otherwise.
##
DeclareAttribute( "Divisor", IsRcwaMapping );
DeclareAttribute( "Divisor", IsRcwaGroup );
DeclareSynonym( "Div", Divisor );

#############################################################################
##
#A  PrimeSet( <f> ) . . . . . . . . . . . . prime set of the rcwa mapping <f>
##
##  Prime set of rcwa mapping <f>.
##
##  We define the *prime set* of an rcwa mapping <f> by the set of all primes
##  dividing the modulus of <f> or some coefficient occuring as factor in the
##  numerator or as denominator.
##
##  We define the *prime set* of and rcwa group by the union of the prime
##  sets of its elements.
##
DeclareAttribute( "PrimeSet", IsRcwaMapping );
DeclareAttribute( "PrimeSet", IsRcwaGroup );

#############################################################################
##
#P  IsIntegral( <f> ) . . . . . indicates whether the divisor of <f> equals 1
#P  IsIntegral( <G> ) . .  indicates whether all elements of <G> are integral
##
##  We say that an rcwa mapping is *integral* if and only if its divisor is
##  equal to 1, and that an rcwa group is *integral* if all of its elements
##  are so.
##
DeclareProperty( "IsIntegral", IsRcwaMapping );
DeclareProperty( "IsIntegral", IsRcwaGroup );

#############################################################################
##
#P  IsBalanced( <f> ) . .  indicates whether or not <f> is a balanced mapping
##
##  We say that an rcwa mapping is *balanced* if and only if its multiplier
##  and its divisor have the same prime divisors.
##
DeclareProperty( "IsBalanced", IsRcwaMapping );

#############################################################################
##
#P  IsClassWiseOrderPreserving( <f> ) .  is <f> class-wise order-preserving ?
#P  IsClassWiseOrderPreserving( <G> ) .  is <G> class-wise order-preserving ?
##
##  Indicates whether or not the rcwa mapping <f> / rcwa group <G> of Z or
##  Z_(pi) is class-wise order-preserving.
##
DeclareProperty( "IsClassWiseOrderPreserving", IsRcwaMappingOfZOrZ_pi ); 
DeclareProperty( "IsClassWiseOrderPreserving", IsRcwaGroup );

#############################################################################
##
#A  SetOnWhichMappingIsClassWiseOrderPreserving( <f> )
#A  SetOnWhichMappingIsClassWiseOrderReversing( <f> )
#A  SetOnWhichMappingIsClassWiseConstant( <f> )
##
##  The union of the residue classes (mod Mod(<f>)) on which the rcwa mapping
##  <f> is class-wise order-preserving, class-wise order-reversing resp.
##  class-wise constant.
##
DeclareAttribute( "SetOnWhichMappingIsClassWiseOrderPreserving",
                  IsRcwaMappingOfZOrZ_pi );
DeclareAttribute( "SetOnWhichMappingIsClassWiseOrderReversing",
                  IsRcwaMappingOfZOrZ_pi );
DeclareAttribute( "SetOnWhichMappingIsClassWiseConstant",
                  IsRcwaMappingOfZOrZ_pi );

#############################################################################
##
#O  Multpk( <f>, <p>, <k> )  the elements multiplied by a multiple of <p>^<k>
##
##  The set of elements n of the base ring R which <f> maps to
##  (a_r(m) * n + b_r(m))/c_r(m), where p^k||a_r(m) if k > 0, resp.
##  p^-k||c_r(m) if k < 0 resp. p \nmid a_r(m), c_r(m) if k = 0.
##
DeclareOperation( "Multpk", [ IsRcwaMapping, IsInt, IsInt ] );

#############################################################################
##
#A  FixedPointsOfAffinePartialMappings( <f> )
##
##  The fixed points of the affine partial mappings of the rcwa mapping <f>
##  in the quotient field of the source.
##
DeclareAttribute( "FixedPointsOfAffinePartialMappings", IsRcwaMapping );

#############################################################################
##
#A  LargestSourcesOfAffineMappings( <f> ) .  partition on which <f> is affine
##
##  The coarsest partition of the base ring R on whose elements the rcwa
##  mapping <f> is affine.
##
DeclareAttribute( "LargestSourcesOfAffineMappings", IsRcwaMapping );

#############################################################################
##
#A  IncreasingOn( <f> ) . . . . . . . . . . . set of n such that |n^f| >> |n|
##
##  The union of all residue classes r(m) such that |R/a_r(m)R|>|R/c_r(m)R|,
##  where R denotes the source and m denotes the modulus of <f>.
##
DeclareAttribute( "IncreasingOn", IsRcwaMapping );

#############################################################################
##
#A  DecreasingOn( <f> ) . . . . . . . . . . . set of n such that |n^f| << |n|
##
##  The union of all residue classes r(m) such that |R/a_r(m)R|<|R/c_r(m)R|,
##  where R denotes the source and m denotes the modulus of <f>.
##
DeclareAttribute( "DecreasingOn", IsRcwaMapping );

#############################################################################
##
#A  ImageDensity( <f> ) . . . . . . . . . . . . . . . .  image density of <f>
##
##  The image density of the rcwa mapping <f>.
##  The *image density* of an rcwa mapping measures how "dense" its image is
##  -- an image density > 1 implies that there need to be "overlaps", i.e.
##  that the mapping cannot be injective, a surjective mapping always has
##  image density >= 1, and the image density of any bijective mapping is 1.
##
DeclareAttribute( "ImageDensity", IsRcwaMapping );

#############################################################################
##
#A  Sign( <g> ) . . . . . . . . . . . . the sign of the rcwa mapping <g> of Z
##
##  The *sign* of the rcwa mapping <f>. The sign mapping is an epimorphism
##  from RCWA(Z) to U(Z) = C_2.
##
DeclareAttribute( "Sign", IsRcwaMapping );

#############################################################################
##
#A  Support( <f> ) . . . . . . . . . . .  the support of the rcwa mapping <f>
#A  Support( <G> ) . . . . . . . . . . . .  the support of the rcwa group <G>
#A  MovedPoints( <f> )
#A  MovedPoints( <G> )
##
##  For rcwa mappings and -groups, `Support' and `MovedPoints' are synonyms.
##
DeclareAttribute( "Support", IsRcwaMapping );
DeclareAttribute( "Support", IsRcwaGroup );
DeclareAttribute( "MovedPoints", IsRcwaMapping );
DeclareAttribute( "MovedPoints", IsRcwaGroup );

#############################################################################
##
#O  ImagesSet( <f>, <S> ) . . . . . . image of <S> under the rcwa mapping <f>
#O  \^( <S>, <f> )  . . . . . . . . . image of <S> under the rcwa mapping <f>
#O  PreImagesSet( <f>, <S> )  . .  preimage of <S> under the rcwa mapping <f>
##
DeclareOperation( "ImagesSet", [ IsRcwaMapping, IsListOrCollection ] );
DeclareOperation( "\^", [ IsListOrCollection, IsRcwaMapping ] );
DeclareOperation( "PreImagesSet", [ IsRcwaMapping, IsList ] );

#############################################################################
##
#V  ZeroRcwaMappingOfZ . . . . . . . . . . . . . . . . zero rcwa mapping of Z
##
DeclareGlobalVariable( "ZeroRcwaMappingOfZ" );

#############################################################################
##
#V  IdentityRcwaMappingOfZ . . . . . . . . . . . . identity rcwa mapping of Z
##
DeclareGlobalVariable( "IdentityRcwaMappingOfZ" );

#############################################################################
##
#F  ClassShift( <r>, <m> ) . . . . . . . . . . . . . . .  class shift nu_r(m)
#F  ClassShift( [ <r>, <m> ] )
#P  IsClassShift( <sigma> )
##
DeclareGlobalFunction( "ClassShift" );
DeclareProperty( "IsClassShift", IsRcwaMapping );

#############################################################################
##
#F  ClassUnionShift( <S> ) . . . . . shift of rc.-union <S> by Modulus( <S> )
##
##  The rcwa mapping which maps <S> to <S> + Modulus(<S>) and fixes the
##  complement of <S>.
##
DeclareGlobalFunction( "ClassUnionShift" );

#############################################################################
##
#F  ClassReflection( <r>, <m> ) . . . . . . .  class reflection varsigma_r(m)
#F  ClassReflection( [ <r>, <m> ] )
#P  IsClassReflection( <sigma> )
##
DeclareGlobalFunction( "ClassReflection" );
DeclareProperty( "IsClassReflection", IsRcwaMapping );

#############################################################################
##
#F  ClassTransposition( <r1>, <m1>, <r2>, <m2> ) . . . .  class transposition
#F  ClassTransposition( [ <r1>, <m1>, <r2>, <m2> ] )
#P  IsClassTransposition( <sigma> )
#A  TransposedClasses( <ct> )
##
DeclareGlobalFunction( "ClassTransposition" );
DeclareProperty( "IsClassTransposition", IsRcwaMapping );
DeclareAttribute( "TransposedClasses", IsRcwaMapping );

#############################################################################
##
#O  SplittedClassTransposition( <ct>, <k>, <cross> )
##
##  Class transpositions can be written as products of any given number <k>
##  of class transpositions, as long as the underlying ring has a residue
##  class ring of cardinality <k>.
##
##  This operation computes such a decomposition.
##
DeclareOperation( "SplittedClassTransposition",
                  [ IsRcwaMapping and IsClassTransposition,
                    IsRingElement ] );
DeclareOperation( "SplittedClassTransposition",
                  [ IsRcwaMapping and IsClassTransposition,
                    IsRingElement, IsBool ] );

#############################################################################
##
#F  ClassPairs( <m> )
##
##  This is an auxiliary function for computing pairs of disjoint residue
##  classes with modulus at most <m>.
##
DeclareGlobalFunction( "ClassPairs" );
 
#############################################################################
##
#V  CLASS_PAIRS
#V  CLASS_PAIRS_LARGE
##
##  Residues and moduli of pairs of disjoint residue classes.
##  Mainly used to generate random class transpositions.
##
DeclareGlobalVariable( "CLASS_PAIRS" );
DeclareGlobalVariable( "CLASS_PAIRS_LARGE" );

#############################################################################
##
#F  PrimeSwitch( <p> ) . . product of ct's, with multiplier <p> and divisor 2
#F  PrimeSwitch( <p>, <k> )
#P  IsPrimeSwitch( <sigma> )
##
DeclareGlobalFunction( "PrimeSwitch" );
DeclareProperty( "IsPrimeSwitch", IsRcwaMapping );

#############################################################################
##
#F  mKnot( <m> ) . . . . . . . . . . rcwa mapping of Timothy P. Keller's type
##
##  Given an odd integer <m>, this function returns the bijective rcwa
##  mapping g_m as defined in
##
##  Timothy P. Keller. Finite Cycles of Certain Periodically Linear
##  Permutations. Missouri J. Math. Sci. 11(1999), no. 3, 152-157.
##
DeclareGlobalFunction( "mKnot" );

#############################################################################
##
#A  FactorizationIntoCSCRCT( <g> )
##
##  A factorization of an element of RCWA(Z) into class shifts,
##  class reflections and class transpositions.
##
DeclareAttribute( "FactorizationIntoCSCRCT", IsMultiplicativeElement );
DeclareSynonym( "FactorizationIntoGenerators", FactorizationIntoCSCRCT );

#############################################################################
##
#P  IsTame( <f> ) . . . . indicates whether or not <f> is a tame rcwa mapping
#P  IsTame( <G> ) . . . . indicates whether or not <G> is a tame rcwa group
##
##  We say that an rcwa mapping <f> is *tame* if and only if the moduli
##  of its powers are bounded, and *wild* otherwise. We say that an rcwa
##  group is *tame* if and only if the moduli of its elements are bounded.
##
DeclareProperty( "IsTame", IsRcwaMapping );
DeclareProperty( "IsTame", IsRcwaGroup );

#############################################################################
##
#O  TransitionMatrix( <f>, <m> ) . . transition matrix of <f> for modulus <m>
##
##  The *transition matrix* T of <f> for modulus <m>.
##
##  The entry T_(i,j) is the "proportion" of the elements of the <i>th
##  residue class which are mapped to the <j>th residue class under <f>.
##  The numbering of the residue classes is the same as in the corresponding
##  return value of the function `AllResidues'.
##
DeclareOperation( "TransitionMatrix", [ IsRcwaMapping, IsRingElement ] );

#############################################################################
##
#F  TransitionSets( <f>, <m> ) . . . . . . . . . . . .  set transition matrix
##
##  The *set transition matrix* <T> of <f> for modulus <m>.
##
##  The entry T_(i,j) is the subset of the <i>th residue class which is
##  mapped to the <j>th residue class under <f>. The numbering of the residue
##  classes is the same as in the corresponding return value of the function
##  `AllResidues'.
##
DeclareGlobalFunction( "TransitionSets" );

#############################################################################
##
#O  TransitionGraph( <f>, <m> ) . .  transition graph of the rcwa mapping <f>
##
##  Transition graph for modulus <m> of the rcwa mapping <f>.
##
##  We define the *transition graph* Gamma_(f,m) for modulus m of an
##  rcwa mapping f as follows:
##
##  - The vertices are the residue classes (mod m).
##
##  - There is an edge from r_1(m) to r_2(m) if and only if there is some
##    n_1 in r_1(m) such that n_1^f in r_2(m).
##
DeclareOperation( "TransitionGraph", [ IsRcwaMapping, IsRingElement ] );

#############################################################################
##
#O  OrbitsModulo( <f>, <m> ) . . . orbit partition of R/mR under `Group(<f>)'
#O  OrbitsModulo( <G>, <m> ) . . . . . . .  orbit partition of R/mR under <G>
##
##  Returns the set of the sets of vertices of the weakly-connected
##  components of the transition graph Gamma_(f,m), resp. an orbit partition
##  of R/mR under <G>.
##
DeclareOperation( "OrbitsModulo", [ IsRcwaMapping, IsRingElement ] );
DeclareOperation( "OrbitsModulo", [ IsRcwaGroup, IsRingElement ] );

#############################################################################
##
#O  FactorizationOnConnectedComponents( <f>, <m> )
##
##  Returns the set of restrictions of the rcwa mapping <f> onto the
##  weakly-connected components of its transition graph Gamma_(f,m).
##  These mappings have pairwisely disjoint supports, hence any two of them
##  commute, and their product equals <f>.
##
DeclareOperation( "FactorizationOnConnectedComponents",
                  [ IsRcwaMapping, IsRingElement ] );

#############################################################################
##
#A  Sources( <f> )
#A  Sinks( <f> )
#A  Loops( <f> )
##
##  Let <f> be an rcwa mapping with modulus m. Then, `Sources(<f>)' and
##  `Sinks(<f>)' are lists of unions of residue classes (mod m), and
##  `Loops(<f>)' is a list of residue classes (mod m).
##
##  The list `Sources(<f>)' contains an entry for any strongly connected
##  component of the transition graph of <f> for modulus m which has only
##  outgoing edges. The list entry corresponding to a given such strongly
##  connected component is just the union of its vertices. The description of
##  the list `Sinks(<f>)' is obtained by replacing "outgoing" by "ingoing".
##
##  The entries of the list `Loops(<f>)' are the residue classes (mod m)
##  which are not setwisely fixed by <f>, but which intersect nontrivially
##  with their images under <f>.
##
DeclareAttribute( "Sources", IsRcwaMapping );
DeclareAttribute( "Sinks", IsRcwaMapping );
DeclareAttribute( "Loops", IsRcwaMapping );

#############################################################################
##
#O  ShortCycles( <f>, <S>, <maxlng> ) .  short cycles of the rcwa mapping <f>
#O  ShortCycles( <f>, <maxlng> )
##
##  In the 3-argument case, `ShortCycles' computes all finite cycles of the
##  rcwa mapping <f> of length <= <maxlng> which intersect nontrivially with
##  the set <S>. In the 2-argument case, it computes all "single" finite
##  cycles of the rcwa mapping <f> of length <= <maxlng>.
##
DeclareOperation( "ShortCycles",
                  [ IsRcwaMapping, IsListOrCollection, IsPosInt ] );
DeclareOperation( "ShortCycles", [ IsRcwaMapping, IsPosInt ] );

#############################################################################
##
#O  RestrictedPerm( <g>, <S> ) . . . . . .  permutation induced by <g> on <S>
##
DeclareOperation( "RestrictedPerm", [ IsRcwaMapping, IsListOrCollection ] );

#############################################################################
##
#O  PermutationOpNC( <sigma>, <P>, <act> )
##
DeclareOperation( "PermutationOpNC",
                  [ IsObject, IsListOrCollection, IsFunction ] );

#############################################################################
##
#F  InjectiveAsMappingFrom( <f> ) . . . .  some set on which <f> is injective
##
##  Returns some subset S of Source(<f>) such that the restriction of <f>
##  to S is injective.
##
DeclareGlobalFunction( "InjectiveAsMappingFrom" );

#############################################################################
##
#A  RightInverse( <f> ) . . . . . . . . . . . . . . . .  right inverse of <f>
##
##  The right inverse of <f>, i.e. a mapping g such that fg = 1.
##  The mapping <f> must be injective.
##
DeclareAttribute( "RightInverse", IsRcwaMapping );

#############################################################################
##
#O  CommonRightInverse( <l>, <r> ) . . . . .  mapping d such that ld = rd = 1
##
##  Returns a mapping d such that ld = rd = 1.
##  The mappings <l> and <r> must be injective, and their images must form
##  a partition of the underlying ring.
##
DeclareOperation( "CommonRightInverse", [ IsRcwaMapping, IsRcwaMapping ] );

#############################################################################
##
#A  LaTeXName( <obj> ) . . . . . . . . . . . .  LaTeX string for object <obj>
##
DeclareAttribute( "LaTeXName", IsObject );

#############################################################################
##
#O  LaTeXAndXDVI( <obj> ) .  write LaTeX string to file, LaTeX & show by xdvi
##
DeclareOperation( "LaTeXAndXDVI", [ IsObject ] );

#############################################################################
##
#O  Trajectory( <f>, <n>, <length> ) . . .  trajectory of <f> starting at <n>
#O  Trajectory( <f>, <n>, <length>, <m> )
#O  Trajectory( <f>, <n>, <length>, <whichcoeffs> )
#O  Trajectory( <f>, <n>, <terminal> )
#O  Trajectory( <f>, <n>, <terminal>, <m> )
#O  Trajectory( <f>, <n>, <terminal>, <whichcoeffs> )
##
##  In the first case, this operation computes the first <length> iterates in
##  the trajectory of the rcwa mapping <f> starting at <n>. In the forth case
##  it computes the initial part of the trajectory of <f> starting at <n>
##  which ends at the first occurence of an iterate in the set <terminal>.
##  In place of the ring element <n>, a finite set of ring elements or a
##  union of residue classes can be given. In the second and fifth case the
##  iterates are reduced (mod <m>) to save memory.
##
##  In the third and sixth case the operation computes "accumulated coeffi-
##  cients" on the trajectory of <n> under the rcwa mapping <f>. The term
##  "accumulated coefficients" denotes the list c of coefficient triples
##  such that for any k we have <n>^(<f>^(k-1)) = (c[k][1]*<n> + c[k][2])/
##  c[k][3]. The argument <whichcoeffs> can either be "AllCoeffs" or
##  "LastCoeffs", and determines whether the entire list of triples or only
##  the last triple is computed.
##
DeclareOperation( "Trajectory", [ IsRcwaMapping, IsObject, IsObject ] );
DeclareOperation( "Trajectory", [ IsRcwaMapping, IsObject, IsObject,
                                                 IsObject ] );

#############################################################################
##
#F  TraceTrajectoriesOfClasses( <f>, <classes> ) . residue class trajectories
##
##  Traces the trajectories of the residue classes in the residue class union
##  <classes> under the mapping <f>. All iterates are written as a list of
##  single residue classes. This list is computed using the function
##  `AsUnionOfFewClasses' from the `ResClasses' package.
##
##  The function stops once it detects a cycle or it detects that a timeout
##  given as option "timeout" has expired.
##
##  Caution: All classes are traced separately, thus a cycle in the
##           trajectory usually does only cause a cycle in the list of
##           *unions* of the returned sets of residue classes!
##
DeclareGlobalFunction( "TraceTrajectoriesOfClasses" );

#############################################################################
##
#O  LikelyContractionCentre( <f>, <maxn>, <bound> ) likely contraction centre
##
##  Tries to compute the *contraction centre* of the rcwa mapping <f>.
##  Assuming its existence, this is the unique finite subset S_0 of the
##  base ring R which <f> maps bijectively onto itself and which intersects
##  nontrivially with any trajectory of <f>. The mapping <f> is assumed to
##  be contracting.
##      As in general contraction centres are likely not computable, methods
##  will be probabilistic. The argument <maxn> is a bound on the starting 
##  value and <bound> is a bound on the elements of the sequence to be
##  searched. If the limit <bound> is exceeded, an Info message on Info level
##  3 of InfoRCWA is given.
##
DeclareOperation( "LikelyContractionCentre",
                  [ IsRcwaMapping, IsRingElement, IsPosInt ] );
DeclareSynonym( "LikelyContractionCenter", LikelyContractionCentre );

#############################################################################
##
#O  GuessedDivergence( <f> ) . . . . . . . . . . .  guessed divergence of <f>
##
##  Guesses the "divergence" of the rcwa mapping <f>.
##  This should give a rough hint on how fast an rcwa mapping contracts
##  (if its divergence is smaller than 1) or how fast its trajectories
##  diverge (if its divergence is larger than 1). Nothing particular is
##  guaranteed, and no mathematical conclusions can be made from the return
##  values. 
##
DeclareOperation( "GuessedDivergence", [ IsRcwaMapping ] );

#############################################################################
##
#E  rcwamap.gd . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here