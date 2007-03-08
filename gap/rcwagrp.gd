#############################################################################
##
#W  rcwagrp.gd                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains declarations of functions, operations etc. for
##  computing with rcwa groups.
##
##  See the definitions given in the file rcwamap.gd.
##
Revision.rcwagrp_gd :=
  "@(#)$Id$";

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
#C  IsRcwaGroupOverZ_pi . . . . . . . . . . . . . . . rcwa groups over Z_(pi)
#C  IsRcwaGroupOverGFqx . . . . . . . . . . . . . . rcwa groups over GF(q)[x]
#C  IsRcwaGroupOverZOrZ_pi . . . . . . . . . . . rcwa groups over Z or Z_(pi)
##
##  The category of all rcwa groups over Z, over semilocalizations of Z, or
##  over polynomial rings in one variable over a finite field, respectively.
##  The category `IsRcwaGroupOverZOrZ_pi' is the union of `IsRcwaGroupOverZ'
##  and `IsRcwaGroupOverZ_pi'.
##
DeclareSynonym( "IsRcwaGroupOverZ",
                 CategoryCollections(IsRcwaMappingOfZ) and IsGroup );
DeclareSynonym( "IsRcwaGroupOverZ_pi",
                 CategoryCollections(IsRcwaMappingOfZ_pi) and IsGroup );
DeclareSynonym( "IsRcwaGroupOverGFqx",
                 CategoryCollections(IsRcwaMappingOfGFqx) and IsGroup );
DeclareSynonym( "IsRcwaGroupOverZOrZ_pi",
                 CategoryCollections(IsRcwaMappingOfZOrZ_pi) and IsGroup );

#############################################################################
##
#V  TrivialRcwaGroupOverZ . . . . . . . . . . . . . trivial rcwa group over Z
#V  TrivialRcwaGroup
##
DeclareGlobalVariable( "TrivialRcwaGroupOverZ" );
DeclareSynonym( "TrivialRcwaGroup", TrivialRcwaGroupOverZ );

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
DeclareGlobalFunction( "RCWA" );

#############################################################################
##
#P  IsNaturalRCWA( <G> ) . . . . . . . . . . . . . . . . . . . . .  RCWA( R )
#P  IsNaturalRCWA_Z( <G> ) . . . . . . . . . . . . . . . . . . . .  RCWA( Z )
#P  IsNaturalRCWA_Z_pi( <G> )  . . . . . . . . . . . . . . . . RCWA( Z_(pi) )
#P  IsNaturalRCWA_GFqx( <G> )  . . . . . . . . . . . . . . . RCWA( GF(q)[x] )
##
DeclareProperty( "IsNaturalRCWA", IsRcwaGroup );
DeclareProperty( "IsNaturalRCWA_Z", IsRcwaGroup );
DeclareProperty( "IsNaturalRCWA_Z_pi", IsRcwaGroup );
DeclareProperty( "IsNaturalRCWA_GFqx", IsRcwaGroup );

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
#A  Sign( <g> ) . . . . . . . . . .  the sign of the element <g> of RCWA( Z )
##
##  The *sign* of the rcwa permutation <g>.
##  The sign mapping is an epimorphism from RCWA(Z) to U(Z) = C_2.
##
DeclareAttribute( "Sign", IsRcwaMapping );

#############################################################################
##
#O  CTCons( <R> ) . . . . . . . . . . . . . . . . . . . .  CT( R ) for ring R
#F  CT( <R> ) . . . . . . . . . . . . . . . . . . . . . .  CT( R ) for ring R
##
DeclareConstructor( "CTCons", [ IsRcwaGroup, IsRing ] );
DeclareGlobalFunction( "CT" );

#############################################################################
##
#P  IsNaturalCT( <G> ) . . . . . . . . . . . . . . . . . . . . . . .  CT( R )
#P  IsNaturalCT_Z( <G> ) . . . . . . . . . . . . . . . . . . . . . .  CT( Z )
#P  IsNaturalCT_Z_pi( <G> )  . . . . . . . . . . . . . . . . . . CT( Z_(pi) )
#P  IsNaturalCT_GFqx( <G> )  . . . . . . . . . . . . . . . . . CT( GF(q)[x] )
##
DeclareProperty( "IsNaturalCT", IsRcwaGroup );
DeclareProperty( "IsNaturalCT_Z", IsRcwaGroup );
DeclareProperty( "IsNaturalCT_Z_pi", IsRcwaGroup );
DeclareProperty( "IsNaturalCT_GFqx", IsRcwaGroup );

#############################################################################
##
#P  IsNaturalRCWA_OR_CT( <G> ) . . . . . . . . . . . . . RCWA( R ) or CT( R )
##
DeclareProperty( "IsNaturalRCWA_OR_CT", IsRcwaGroup );

#############################################################################
##
#S  Constructing rcwa groups. ///////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#O  IsomorphismRcwaGroup( <G>, <R> ) . .  rcwa representation of <G> over <R>
#O  IsomorphismRcwaGroup( <G> )  . . . . .  rcwa representation of <G> over Z
#A  IsomorphismRcwaGroupOverZ( <G> ) . . . . . .  the corresponding attribute
##
##  A faithful rcwa representation of the group <G> over the ring <R>,
##  respectively over Z.
##
DeclareOperation( "IsomorphismRcwaGroup", [ IsGroup, IsRing ] );
DeclareOperation( "IsomorphismRcwaGroup", [ IsGroup ] );
DeclareAttribute( "IsomorphismRcwaGroupOverZ", IsGroup );

#############################################################################
##
#O  Restriction( <g>, <f> ) . . . . . . . . . . . . restriction of <g> by <f>
#O  Restriction( <G>, <f> ) . . . . . . . . . . . . restriction of <G> by <f>
##
##  Computes the *restriction* of the rcwa mapping <g> resp. rcwa group <G>
##  by (i.e. to the image of) the rcwa mapping <f>. The mapping <f> must be
##  injective.
##
DeclareOperation( "Restriction", [ IsRcwaMapping, IsRcwaMapping ] );
DeclareOperation( "Restriction", [ IsRcwaGroup, IsRcwaMapping ] );

#############################################################################
##
#O  Induction( <g>, <f> ) . . . . . . . . . . . . . . induction of <g> by <f>
#O  Induction( <G>, <f> ) . . . . . . . . . . . . . . induction of <G> by <f>
##
##  Computes the *induction* of the rcwa mapping <g> resp. the rcwa group <G>
##  by the rcwa mapping <f>.
##
##  The mapping <f> must be injective, and both the support of <g> and its
##  image under <g>, resp. the support of <G>, must lie in the image of <f>.
##  We have Induction( Restriction( <g>, <f> ), <f> ) = <g> as well as
##  Induction( Restriction( <G>, <f> ), <f> ) = <G>. Therefore induction is
##  the right inverse of restriction.
##
DeclareOperation( "Induction", [ IsRcwaMapping, IsRcwaMapping ] );
DeclareOperation( "Induction", [ IsRcwaGroup, IsRcwaMapping ] );

#############################################################################
##
#S  The action of an rcwa group on the underlying ring. /////////////////////
##
#############################################################################

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
#O  ShortOrbits( <G>, <S>, <maxlng> ) . . . .  short orbits of rcwa group <G>
##
##  Computes all finite orbits of the rcwa group <G> of length <= <maxlng>,
##  which intersect nontrivially with the set <S>.
##
DeclareOperation( "ShortOrbits", [ IsGroup, IsListOrCollection, IsPosInt ] );

#############################################################################
##
#O  RepresentativeActionPreImage( <G>, <src>, <dest>, <act>, <F> )
#O  RepresentativesActionPreImage( <G>, <src>, <dest>, <act>, <F> )
##
##  Computes a preimage resp. possibly multiple preimages of an element of
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
#O  Ball( <G>, <g>, <d> )  ball of diameter <d> around the element <g> of <G>
#O  Ball( <G>, <p>, <d>, <act> )   "    the point <p> under the action of <G>
##
##  All balls are understood w.r.t. the stored generators of the group <G>.
##
DeclareOperation( "Ball", [ IsGroup, IsObject, IsInt ] );
DeclareOperation( "Ball", [ IsGroup, IsObject, IsInt, IsFunction ] );

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
#A  ModulusOfRcwaGroup( <G> ) . . . . . . . . . modulus of the rcwa group <G>
##
##  We define the *modulus* of an rcwa group by the lcm of the moduli of its
##  elements in case such an lcm exists, and by 0 otherwise. 
##
DeclareAttribute( "ModulusOfRcwaGroup", IsRcwaGroup );

#############################################################################
##
#A  RespectedPartition( <G> ) . . . . . . . . . . . . . . respected partition
#A  RespectedPartition( <sigma> )
#A  RespectedPartitionShort( <G> )
#A  RespectedPartitionShort( <sigma> )
#A  RespectedPartitionLong( <G> )
#A  RespectedPartitionLong( <sigma> )
##
##  A partition of the base ring R into a finite number of residue classes
##  on which the rcwa group <G> acts as a permutation group, and on whose
##  elements all elements of <G> are affine. Provided that R has a residue
##  class ring of cardinality 2, such a partition exists if and only if <G>
##  is tame. The respected partition of a bijective rcwa mapping <sigma> is
##  defined as the respected partition of the cyclic group generated by
##  <sigma>. `RespectedPartitionShort' is a respected partition whose ele-
##  ments have at most modulus Mod(<G>), and `RespectedPartitionLong' is a
##  respected partition whose elements have at least modulus Mod(<G>).
##
DeclareAttribute( "RespectedPartitionShort", IsObject );
DeclareAttribute( "RespectedPartitionLong", IsObject );
DeclareSynonym( "RespectedPartition", RespectedPartitionShort );
DeclareSynonym( "SetRespectedPartition", SetRespectedPartitionShort );
DeclareSynonym( "HasRespectedPartition", HasRespectedPartitionShort );

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
##  Some integral conjugate of the rcwa mapping <g> resp. rcwa group <G> in
##  RCWA(R). Such a conjugate exists always if <g> is a tame bijective rcwa
##  mapping resp. if <G> is a tame rcwa group, and the underlying ring R has
##  residue class rings of any finite cardinality. Integral conjugates are
##  of course not unique.
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
#S  Miscellanea. ////////////////////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#A  RankOfFreeGroup( <Fn> )
##
DeclareAttribute( "RankOfFreeGroup", IsRcwaGroup );

#############################################################################
##
#O  Projections( <G>, <m> )  projections to unions of residue classes (mod m)
##
DeclareOperation( "Projections", [ IsRcwaGroup, IsRingElement ] );

#############################################################################
##
#O  RepresentativeActionOp( <G>, <g>, <h>, <act> )
##
DeclareOperation( "RepresentativeActionOp",
                  [ IsGroup, IsObject, IsObject, IsFunction ] );

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
#O  Factorization( [ <G>, ], <g> ) . . . . . .  factorization into generators
##
##  If `Factorization' is not yet an operation, turn it into one and install
##  the GAP library function of the same name as a method for it.
##
if not IsOperation( Factorization ) then
  DefaultFactorization := Factorization;
  MakeReadWriteGlobal( "Factorization" ); Unbind( Factorization );
  DeclareOperation( "Factorization",
                    [ IsGroup, IsMultiplicativeElementWithInverse ] );
  InstallMethod( Factorization,"default method", true,
               [ IsGroup, IsMultiplicativeElementWithInverse ], 0,
               DefaultFactorization );
fi;
DeclareOperation( "Factorization",
                  [ IsMultiplicativeElementWithInverse ] );

#############################################################################
##
#E  rcwagrp.gd . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here