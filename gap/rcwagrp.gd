#############################################################################
##
#W  rcwagrp.gd                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains declarations of functions, operations etc. for
##  computing with rcwa groups.
##
##  See the definitions given in the file `rcwamap.gd'.
##
##  We call a subgroup of RCWA($R$) a *residue class-wise affine* group, or
##  in short an *rcwa* group. We define the *modulus* of an rcwa group by
##  the lcm of the moduli of its elements in case such an lcm exists,
##  and by 0 otherwise. 
##
Revision.rcwagrp_gd :=
  "@(#)$Id$";

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
#C  IsRcwaGroupOverZ . . . . . . . . . . . . . . . . . . . rcwa groups over Z
##
##  The category of all rcwa groups over $\Z$.
##
DeclareSynonym( "IsRcwaGroupOverZ",
                 CategoryCollections(IsRcwaMappingOfZ) and IsGroup );

#############################################################################
##
#C  IsRcwaGroupOverZ_pi . . . . . . . . . . . . . . . rcwa groups over Z_(pi)
##
##  The category of all rcwa groups over semilocalizations of $\Z$.
##
DeclareSynonym( "IsRcwaGroupOverZ_pi",
                 CategoryCollections(IsRcwaMappingOfZ_pi) and IsGroup );

#############################################################################
##
#C  IsRcwaGroupOverZOrZ_pi . . . . . . . . . . . rcwa groups over Z or Z_(pi)
##
##  The category of all rcwa groups over the ring $\Z$ or semilocalizations
##  thereof. This is the union of the categories `IsRcwaGroupOverZ' and
##  `IsRcwaGroupOverZ_pi'.
##
DeclareSynonym( "IsRcwaGroupOverZOrZ_pi",
                 CategoryCollections(IsRcwaMappingOfZOrZ_pi) and IsGroup );

#############################################################################
##
#C  IsRcwaGroupOverGFqx . . . . . . . . . . . . . . rcwa groups over GF(q)[x]
##
##  The category of all rcwa groups over polynomial rings in one variable
##  over finite fields.
##
DeclareSynonym( "IsRcwaGroupOverGFqx",
                 CategoryCollections(IsRcwaMappingOfGFqx) and IsGroup );

#############################################################################
##
#C  CategoryCollections( IsRcwaMappingOfZ ) . . . . . . . rcwa domains over Z
##
##  The category of all domains formed out of rcwa mappings of Z.
##
DeclareCategoryCollections( "IsRcwaMappingOfZ" );

#############################################################################
##
#V  TrivialRcwaGroupOverZ( <G> ) . . . . . . . . .  trivial rcwa group over Z
#V  TrivialRcwaGroup( <G> )
##
DeclareGlobalVariable( "TrivialRcwaGroupOverZ" );
DeclareSynonym( "TrivialRcwaGroup", TrivialRcwaGroupOverZ );

#############################################################################
##
#O  RCWACons( <R> ) . . . . . . . . . . . . . . . . . RCWA( <R> ) for PID <R>
##
DeclareConstructor( "RCWACons", [ IsRcwaGroup, IsRing ] );

#############################################################################
##
#F  RCWA( <R> ) . . . . . . . . . . . . . . . . . . . RCWA( <R> ) for PID <R>
##
DeclareGlobalFunction( "RCWA" );

#############################################################################
##
#P  IsNaturalRCWA_Z( <G> ) . . . . . . . . . . . . . . . . . . . .  RCWA( Z )
##
DeclareProperty( "IsNaturalRCWA_Z", IsRcwaGroup );

#############################################################################
##
#P  IsNaturalRCWA_Z_pi( <G> ) . . . . . . . . . . . . . . . . .  RCWA( Z_pi )
##
DeclareProperty( "IsNaturalRCWA_Z_pi", IsRcwaGroup );

#############################################################################
##
#P  IsNaturalRCWA_GF_q_x( <G> ) . . . . . . . . . . . . . .  RCWA( GF(q)[x] )
##
DeclareProperty( "IsNaturalRCWA_GF_q_x", IsRcwaGroup );

#############################################################################
##
#F  NrConjugacyClassesOfRCWAZOfOrder( <ord> ) . #Ccl of RCWA(Z) / order <ord>
##
##  Computes the number of conjugacy classes of the whole group RCWA(Z) of
##  elements of order <ord>.
##
DeclareGlobalFunction( "NrConjugacyClassesOfRCWAZOfOrder" );

#############################################################################
##
#A  ModulusOfRcwaGroup( <G> ) . . . . . . . . . modulus of the rcwa group <G>
##
DeclareAttribute( "ModulusOfRcwaGroup", IsRcwaGroup );

#############################################################################
##
#P  IsTame( <G> ) . . . . . indicates whether or not <G> is a tame rcwa group
##
##  We say that an $R$-rcwa group is *tame* if and only if its modulus is
##  strictly positive, and *wild* otherwise.
##
DeclareProperty( "IsTame", IsRcwaGroup );

#############################################################################
##
#A  PrimeSet( <G> ) . . . . . . . . . . . . . prime set of the rcwa group <G>
##
##  Prime set of rcwa group <G>.
##
##  We define the prime set of an rcwa group <G> by the union of the prime
##  sets of its elements.
##
DeclareAttribute( "PrimeSet", IsRcwaGroup );

#############################################################################
##
#P  IsIntegral( <G> ) . . . . . . .  indicates whether or not <G> is integral
##
##  We say that an $R$-rcwa group is *integral* if and only if all of its
##  elements are integral.
##
DeclareProperty( "IsIntegral", IsRcwaGroup ); 

#############################################################################
##
#P  IsClassWiseOrderPreserving( <G> ) .  is <G> class-wise order-preserving ?
##
##  Indicates whether <G> is class-wise order-preserving or not.
##
##  We say that an rcwa group <G> over $\Z$ is *class-wise order-preserving*
##  if all of its elements are.
##
DeclareProperty( "IsClassWiseOrderPreserving", IsRcwaGroupOverZ ); 

#############################################################################
##
#O  ShortOrbits( <G>, <S>, <maxlng> ) . . . .  short orbits of rcwa group <G>
##
##  Computes all finite orbits of the rcwa group <G> of maximal length
##  <maxlng>, which intersect non-trivially with the set <S>.
##
DeclareOperation( "ShortOrbits", [ IsGroup, IsListOrCollection, IsPosInt ] );

#############################################################################
##
#O  OrbitUnion( <G>, <S> ) . . . . . . .  union of the orbit of <S> under <G>
##
##  Computes the union of the elements of the orbit of the set <S> under
##  the rcwa group <G>. In particular, <S> can be a union of residue classes.
##
DeclareOperation( "OrbitUnion", [ IsRcwaGroup, IsListOrCollection ] );

#############################################################################
##
#O  PreImagesRepresentatives( <map>, <elm> ) . . . .  several representatives
##
##  An analogon to `PreImagesRepresentative' which returns a list of possibly
##  several representatives if computing these is not harder than computing
##  just one representative.
##
DeclareOperation( "PreImagesRepresentatives",
                  [ IsGeneralMapping, IsObject ] );

#############################################################################
##
#O  RepresentativeActionPreImage( <G>, <src>, <dest>, <act>, <F> )
##
##  Computes the preimage of an element of <G> which maps <src> to <dest>
##  under the natural projection from the free group <F> onto <G>.
##  The rank of <F> must be equal to the number of generators of <G>.
##
DeclareOperation( "RepresentativeActionPreImage",
                  [ IsGroup, IsObject, IsObject,
                    IsFunction, IsFreeGroup ] );

#############################################################################
##
#O  RepresentativesActionPreImage( <G>, <src>, <dest>, <act>, <F> )
##
##  An analogon to `RepresentativeActionPreImage' which returns a list of
##  possibly several representatives if computing these is not harder than
##  computing just one representative.
##
DeclareOperation( "RepresentativesActionPreImage",
                  [ IsGroup, IsObject, IsObject,
                    IsFunction, IsFreeGroup ] );

#############################################################################
##
#A  RespectedPartition( <G> ) . . . . . . . . . . . . . . respected partition
#A  RespectedPartition( <sigma> )
#A  RespectedPartitionShort( <G> )
#A  RespectedPartitionShort( <sigma> )
##
##  A partition of the base ring <R> into a finite number of residue classes
##  on which the rcwa group <G> acts as a permutation group, and on whose
##  elements all elements of <G> are affine. Provided that <R> has a residue
##  class ring of cardinality 2, such a partition exists if and only if <G>
##  is tame. The respected partition of a bijective rcwa mapping <sigma> is
##  defined as the respected partition of the cyclic group generated by
##  <sigma>. `RespectedPartitionShort' is a respected partition whose ele-
##  ments have at most modulus Mod(<G>).
##
DeclareAttribute( "RespectedPartition", IsObject );
DeclareAttribute( "RespectedPartitionShort", IsObject );

#############################################################################
##
#A  ActionOnRespectedPartition( <G> ) .  action of <G> on respected partition
##
##  The action of the tame group <G> on its stored respected partition.
##
DeclareAttribute( "ActionOnRespectedPartition", IsRcwaGroup );

#############################################################################
##
#A  RankOfKernelOfActionOnRespectedPartition( <G> )
##
##  The rank of the largest free abelian group fitting into the kernel of the
##  action of <G> on its respected partition. The group <G> has to be tame.
##
DeclareAttribute( "RankOfKernelOfActionOnRespectedPartition", IsRcwaGroup );

#############################################################################
##
#A  KernelOfActionOnRespectedPartition( <G> )
##
##  The kernel of the action of <G> on its respected partition.
##  The group <G> has to be tame.
##
DeclareAttribute( "KernelOfActionOnRespectedPartition", IsRcwaGroup );

#############################################################################
##
#A  KernelOfActionOnRespectedPartitionHNFMat( <G> )
##
##  A matrix of row vectors spanning the lattice corresponding to
##  KernelOfActionOnRespectedPartition( <G> ), in Hermite normal form.
##
DeclareAttribute( "KernelOfActionOnRespectedPartitionHNFMat",
                  IsRcwaGroupOverZ );

#############################################################################
##
#A  IsomorphismMatrixGroup( <G> ) . . . . . . .  matrix representation of <G>
##
DeclareAttribute( "IsomorphismMatrixGroup", IsGroup );

#############################################################################
##
#A  IsomorphismRcwaGroupOverZ( <G> ) . . . . . . . rcwa representation of <G>
#A  IsomorphismRcwaGroup( <G> )
##
##  A faithful rcwa representation of the group <G> over $\Z$.
##
DeclareAttribute( "IsomorphismRcwaGroupOverZ", IsGroup );
DeclareSynonym( "IsomorphismRcwaGroup", IsomorphismRcwaGroupOverZ );
DeclareSynonym( "IsomorphismIntegralRcwaGroup", IsomorphismRcwaGroupOverZ );

#############################################################################
##
#F  RcwaGroupOverZByPermGroup( <G> ) . . . . . . rcwa group isomorphic to <G>
#F  RcwaGroupByPermGroup( <G> )
##
##  Constructs an integral rcwa group isomorphic to the permutation
##  group <G>, which acts on [ 1 .. LargestMovedPoint( <G> ) ] as <G> does.
##
DeclareGlobalFunction( "RcwaGroupOverZByPermGroup" );
DeclareSynonym( "RcwaGroupByPermGroup", RcwaGroupOverZByPermGroup );
DeclareSynonym( "IntegralRcwaGroupByPermGroup", RcwaGroupOverZByPermGroup );

#############################################################################
##
#A  IntegralizingConjugator( <f> ) . . . . . mapping <x>: <f>^<x> is integral
#A  IntegralizingConjugator( <G> ) . . . . . mapping <x>: <G>^<x> is integral
##
##  A mapping <x> such that <f>^<x> resp. <G>^<x> is integral. Exists always
##  if <f> is a tame bijective rcwa mapping resp. if <G> is a tame rcwa
##  group, and the underlying ring <R> has residue class rings of any finite
##  cardinality.
##
DeclareAttribute( "IntegralizingConjugator", IsRcwaMapping );

#############################################################################
##
#A  IntegralConjugate( <f> ) . . . . . . . . . . .  integral conjugate of <f>
#A  IntegralConjugate( <G> ) . . . . . . . . . . .  integral conjugate of <G>
##
##  Some integral conjugate of the rcwa mapping <f> resp. rcwa group <G>
##  in RCWA(<R>). This is certainly not defined uniquely, and exists only
##  if <f> is tame.
##  
DeclareAttribute( "IntegralConjugate", IsRcwaMapping );

#############################################################################
##
#A  StandardizingConjugator( <f> ) . . . . . mapping <x>: <f>^<x> is standard
#A  StandardizingConjugator( <G> ) . . . . . mapping <x>: <G>^<x> is standard
##
##  A mapping <x> such that <f>^<x> resp. <G>^<x> is the ``standard''
##  representative of the conjugacy class resp. conjugacy class of subgroups
##  of RCWA(<R>) the bijective rcwa mapping <f> resp. the rcwa group <G>
##  belongs to.
##
DeclareAttribute( "StandardizingConjugator", IsRcwaMapping );

#############################################################################
##
#A  StandardConjugate( <f> ) . .  standard rep. of the conjugacy class of <f>
#A  StandardConjugate( <G> ) . .  standard rep. of the conjugacy class of <G>
##
##  Some ``nice'' canonical representative of the conjugacy class of the
##  bijective rcwa mapping <f> / rcwa group <G> in the whole group RCWA(<R>).
##  Two rcwa mappings / rcwa groups are conjugate in RCWA(<R>) if and only if
##  their ``standard conjugates'' are equal.
##
DeclareAttribute( "StandardConjugate", IsRcwaMapping );

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
#O  Ball( <G>, <g>, <d> )  ball of diameter <d> around the element <g> of <G>
#O  Ball( <G>, <p>, <d> )        "      the point <p> under the action of <G>
##
##  All balls are understood w.r.t. the stored generators of the group <G>.
##
DeclareOperation( "Ball", [ IsGroup, IsObject, IsPosInt ] );

#############################################################################
##
#F  GeneratorsAndInverses( <G> ) list of generators of <G> and their inverses
##
DeclareGlobalFunction( "GeneratorsAndInverses" );

#############################################################################
##
#F  EpimorphismByGenerators( <F>, <G> ) .  epi.: gen's of <F> -> gen's of <G>
#F  EpimorphismByGeneratorsNC( <F>, <G> )
##
DeclareGlobalFunction( "EpimorphismByGenerators" );
DeclareGlobalFunction( "EpimorphismByGeneratorsNC" );

#############################################################################
##
#E  rcwagrp.gd . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here