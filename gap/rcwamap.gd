#############################################################################
##
#W  rcwamap.gd                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains declarations of functions, operations etc. for
##  computing with rcwa mappings.
##
##  Let $R$ be an infinite euclidean domain which is not a field and all of
##  whose proper residue class rings are finite. We call a mapping $f$ from
##  $R$ into itself *residue class-wise affine*, or in short an
##  *rcwa* mapping, if there is a non-zero modulus $m \in R$ such that
##  for any residue class $r(m) \in R/mR$ there are coefficients
##  $a_r, b_r, c_r \in R$ such that the restriction of $f$ to $r(m)$ is
##  given by
##  $$
##    n \ \mapsto \ \frac{a_r \cdot n + b_r}{c_r}.
##  $$
##  We always assume that all fractions are reduced, i.e. that
##  $\gcd( a_r, b_r, c_r ) = 1$, and that $m$ is minimal w.r.t. the given
##  property. Apart from the restrictions imposed by the condition that the
##  image of any residue class $r(m)$ under $f$ must be a subset of $R$ and
##  that we cannot divide by 0, the coefficients $a_r$, $b_r$ and $c_r$ can
##  be any ring elements. We call $m$ the *modulus* of $f$. When talking
##  about the *product* of some rcwa mappings we always mean their
##  composition as mappings, and by the inverse of a bijective rcwa mapping
##  we mean its inverse mapping. 
##
##  The set RCWA($R$) $ \ := \ $ $\{ \ g \in$ Sym($R$) $\ | \ g$ is residue
##  class-wise affine $\}$ is closed under multiplication and taking
##  inverses (this can be verified easily), hence forms a subgroup of
##  Sym($R$). While computing with permutations of infinite sets in general
##  is a very difficult task, the rcwa mappings form a class of permutations
##  which is accessible to computations.
##
##  In order to define an rcwa mapping we need to know about the following:
##
##  \beginitems
##    <Underlying Ring>& The underlying ring $R$ is stored as the
##    `UnderlyingRing' of the family the rcwa mapping object belongs to,
##    and as the value of the attribute `Source'.
##
##    <Modulus>& The modulus is stored as a component <modulus> in any
##    rcwa mapping object. 
##
##    <Coefficients>& The list of coefficients is stored as a component
##    <coeffs> in any rcwa mapping object. The component <coeffs> is a list
##    of $|R$/<modulus>$R|$ lists of three elements of $R$, each, giving
##    the coefficients $a_r$, $b_r$ and $c_r$ for $r$ running through a set
##    of representatives for the residue classes (mod <modulus>).
##    The ordering of these triples is defined by the ordering of the
##    residues $r$ mod <modulus> in the return value of
##    `AllResidues( <R>, <modulus> )'.
##  \enditems
##
##  It is always taken care that the entries of the stored coefficient
##  triples of an rcwa mapping are coprime, that the third entry of any
##  coefficient triple equals its standard conjugate and that the number of
##  stored coefficient triples equals the number of residue classes modulo
##  the modulus of the mapping. Given this, an rcwa mapping determines its
##  internal representation uniquely -- thus testing rcwa mappings for
##  equality is computationally very cheap. The above also prevents
##  unnecessary coefficient explosion.
##
Revision.rcwamap_gd :=
  "@(#)$Id$";

#############################################################################
##
#V  InfoRCWA . . . . . . . . . . . . . . . . . .  info class for RCWA package
##
##  This is the Info class of the RCWA package (see~"ref:Info Functions" 
##  in the {\GAP} Reference Manual for a description of the Info mechanism).
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
#C  IsIntegralRcwaMapping . . . . . . . . . . . . . .  integral rcwa mappings
##
##  The category of all integral rcwa mappings.
##
DeclareCategory( "IsIntegralRcwaMapping", IsRingElement );

#############################################################################
##
#C  IsSemilocalIntegralRcwaMapping . . . . . semilocal integral rcwa mappings
##
##  The category of all semilocal integral rcwa mappings.
##
DeclareCategory( "IsSemilocalIntegralRcwaMapping", IsRingElement );

#############################################################################
##
#C  IsRationalBasedRcwaMapping . . . . . semilocal- or integral rcwa mappings
##
##  The category of all integral or semilocal integral rcwa mappings.
##  This is the union of the categories `IsIntegralRcwaMapping' and
##  `IsSemilocalIntegralRcwaMapping'.
##
DeclareCategory( "IsRationalBasedRcwaMapping", IsRingElement );

#############################################################################
##
#C  IsModularRcwaMapping . . . . . . . . . . . . . . .  modular rcwa mappings
##
##  The category of all modular rcwa mappings.
##
DeclareCategory( "IsModularRcwaMapping", IsRingElement );

#############################################################################
##
#F  RcwaMappingsFamily( <R> ) . . . family of rcwa mappings over the ring <R>
##
DeclareGlobalFunction( "RcwaMappingsFamily" );

#############################################################################
##
#V  IntegralRcwaMappingsFamily . . . the family of all integral rcwa mappings
##
DeclareGlobalVariable( "IntegralRcwaMappingsFamily" );

#############################################################################
##
#F  SemilocalIntegralRcwaMappingsFamily( <primes> )
##
##  Family of semilocal integral rcwa mappings with underlying ring
##  $\Z_{(\pi)}$, where the set $\pi$ is given by the list <primes>.
##
DeclareGlobalFunction( "SemilocalIntegralRcwaMappingsFamily" );

#############################################################################
##
#F  ModularRcwaMappingsFamily( <R> ) . . . .  family of modular rcwa mappings
##
##  Family of modular rcwa mappings with underlying polynomial ring <R>.
##
DeclareGlobalFunction( "ModularRcwaMappingsFamily" );

#############################################################################
##
#R  IsRcwaMappingStandardRep . . . "standard" representation of rcwa mappings
##
##  Representation of rcwa mappings by modulus <modulus> (in the following
##  denoted by $m$) and coefficient list <coeffs>.
##
##  The component <coeffs> is a list of $|R/mR|$ lists of three elements of
##  the underlying ring $R$, each, giving the coefficients $a_r$, $b_r$ and
##  $c_r$ for $r$ running through a set of representatives for the residue
##  classes (mod $m$).
##
##  The ordering of these triples is defined by the ordering of the residues
##  $r$ mod $m$ in the return value of `AllResidues( <R>, <m> )'.
##
DeclareRepresentation( "IsRcwaMappingStandardRep",
                       IsComponentObjectRep and IsAttributeStoringRep,
                       [ "modulus", "coeffs" ] );

#############################################################################
##
#M  RcwaMapping( <R>, <modulus>, <coeffs> )
#M  RcwaMapping( <R>, <coeffs> )
#M  RcwaMapping( <coeffs> )
#M  RcwaMapping( <perm>, <range> )
#M  RcwaMapping( <modulus>, <values> )
#M  RcwaMapping( <pi>, <coeffs> )
#M  RcwaMapping( <q>, <modulus>, <coeffs> )
#M  RcwaMapping( <cycles> )
#M  RcwaMappingNC( <R>, <modulus>, <coeffs> )
#M  RcwaMappingNC( <R>, <coeffs> )
#M  RcwaMappingNC( <coeffs> )
#M  RcwaMappingNC( <perm>, <range> )
#M  RcwaMappingNC( <modulus>, <values> )
#M  RcwaMappingNC( <pi>, <coeffs> )
#M  RcwaMappingNC( <q>, <modulus>, <coeffs> )
#M  RcwaMappingNC( <cycles> )
##
##  Construction of the rcwa mapping 
##
##  \beginlist
##    \item{(a)}
##      of <R> with modulus <modulus> and coefficients <coeffs>, resp.
##    \item{(b)}
##      of $R = \Z$ or $R = \Z_\pi$ with modulus `Length( <coeffs> )'
##      and coefficients <coeffs>, resp.
##    \item{(c)}
##      of $R = \Z$ with modulus `Length( <coeffs> )' and coefficients
##      <coeffs>, resp.
##    \item{(d)}
##      of $R = \Z$, acting on the translates of <range> by integral
##      multiples of the length of <range> as the translates of the finite
##      permutation <perm> to the respective intervals resp.
##    \item{(e)}
##      of $R = \Z$ with modulus <modulus> and values prescribed by the
##      list <values>, which consists of 2 * <modulus> pairs giving preimage
##      and image for 2 points per residue class (mod <modulus>) resp.
##    \item{(f)}
##      of $R = \Z_\pi$ with with modulus `Length( <coeffs> )' and
##      coefficients <coeffs>, resp.
##    \item{(g)}
##      of GF(<q>)[<x>] with modulus <modulus> and coefficients <coeffs>, 
##      resp.
##    \item{(h)}
##      an arbitrary rcwa mapping with residue class cycles as given by
##      <cycles>. The latter is a list of lists of disjoint residue classes
##      which the mapping should permute cyclically, each.
##  \endlist
##
##  The difference between `RcwaMapping' and `RcwaMappingNC'
##  is that the former performs some argument checks which are omitted in the
##  latter, where just anything may happen if wrong or inconsistent arguments
##  are given.
##
DeclareOperation( "RcwaMapping", [ IsObject ] );
DeclareOperation( "RcwaMappingNC", [ IsObject ] );

#############################################################################
##
#F  ClassShift( <S> ) . .  shift of residue class union <S> by Modulus( <S> )
##
##  The rcwa mapping which maps <S> to <S> + `Modulus'(<S>) and fixes the
##  complement of <S>.
##
DeclareGlobalFunction( "ClassShift" );
 
#############################################################################
##
#V  ZeroIntegralRcwaMapping . . . . . . . . . . .  zero integral rcwa mapping
##
DeclareGlobalVariable( "ZeroIntegralRcwaMapping" );

#############################################################################
##
#V  IdentityIntegralRcwaMapping . . . . . . .  identity integral rcwa mapping
##
DeclareGlobalVariable( "IdentityIntegralRcwaMapping" );

#############################################################################
##
#A  Multiplier( <f> ) . . . . . . . .  the multiplier of the rcwa mapping <f>
##
##  We define the *multiplier* of an rcwa mapping <f> by the standard
##  associate of the least common multiple of the coefficients $a_r$.
##
DeclareAttribute( "Multiplier", IsRcwaMapping );

#############################################################################
##
#A  Divisor( <f> ) . . . . . . . . . . .  the divisor of the rcwa mapping <f>
##
##  We define the *divisor* of an rcwa mapping <f> by the standard
##  associate of the least common multiple of the coefficients $c_r$.
##
DeclareAttribute( "Divisor", IsRcwaMapping );

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
DeclareAttribute( "PrimeSet", IsRcwaMapping );

#############################################################################
##
#P  IsTame( <f> ) . . . . indicates whether or not <f> is a tame rcwa mapping
##
##  We say that an rcwa mapping <f> is *tame* if and only if the moduli
##  of its powers are bounded, and *wild* otherwise.
##
DeclareProperty( "IsTame", IsRcwaMapping );

#############################################################################
##
#P  IsIntegral( <f> ) . . . . . . .  indicates whether or not <f> is integral
##
##  We say that an rcwa mapping is *integral* if and only if its divisor is
##  equal to 1. This should not be confused with the term ``integral rcwa
##  mapping'' for an rcwa mapping of the integers.
##
DeclareProperty( "IsIntegral", IsRcwaMapping );

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
##
##  Indicates whether or not the rational-based rcwa mapping <f> is
##  class-wise order-preserving.
##
DeclareProperty( "IsClassWiseOrderPreserving", IsRationalBasedRcwaMapping ); 

#############################################################################
##
#O  Multpk( <f>, <p>, <k> )  the elements multiplied by a multiple of <p>^<k>
##
##  The set of elements $n$ of the base ring $R$, which are mapped to
##  $(a_r n + b_r)/c_r$, where $p^k||a_r$ if $k \gt 0$, resp. $p^{-k}||c_r$
##  if $k \lt 0$ resp. $p \nmid a_r, c_r$ if $k = 0$.
##
DeclareOperation( "Multpk", [ IsRcwaMapping, IsInt, IsInt ] );

#############################################################################
##
#F  TransitionMatrix( <f>, <m> ) . . transition matrix of <f> for modulus <m>
##
##  The *transition matrix* <T> of <f> for modulus <m>.
##
##  The entry $T_{i,j}$ is the ``proportion'' of the elements of the <i>th
##  residue class which are mapped to the <j>th residue class under <f>.
##  The numbering of the residue classes is the same as in the corresponding
##  return value of the function `AllResidues'.
##
DeclareGlobalFunction( "TransitionMatrix" );

#############################################################################
##
#F  TransitionSets( <f>, <m> ) . . . . . . . . . . . .  set transition matrix
##
##  The *set transition matrix* <T> of <f> for modulus <m>.
##
##  The entry $T_{ij}$ is the subset of the <i>th residue class which is
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
##  We define the *transition graph* $\Gamma_{f,m}$ for modulus <m> of the
##  rcwa mapping $f$ as follows:
##  \beginlist
##
##     \item{-} The vertices are the residue classes (mod $m$).
##
##     \item{-} There is an edge from $r_1(m)$ to $r_2(m)$ if and only if
##              there is some $n_1 \in r_1(m)$ such that
##	        $n_1^f \in r_2(m)$.
##
##  \endlist
##
DeclareOperation( "TransitionGraph", [ IsRcwaMapping, IsRingElement ] );

#############################################################################
##
#O  OrbitsModulo( <f>, <m> ) . . orbit partition of $R/mR$ under `Group(<f>)'
##
##  Returns the set of the sets of vertices of the weakly-connected
##  components of the transition graph $\Gamma_{f,m}$.
##
DeclareOperation( "OrbitsModulo", [ IsRcwaMapping, IsRingElement ] );

#############################################################################
##
#O  FactorizationOnConnectedComponents( <f>, <m> )
##
##  Returns the set of restrictions of the rcwa mapping <f> onto the
##  weakly-connected components of its transition graph $\Gamma_{f,m}$.
##  These mappings have pairwisely disjoint supports, hence any two of them
##  commute, and their product equals <f>.
##
DeclareOperation( "FactorizationOnConnectedComponents",
                  [ IsRcwaMapping, IsRingElement ] );

#############################################################################
##
#F  Trajectory( <f>, <n>, <val>, <cond> )
##
##  This function computes the trajectory of <n> under the rcwa mapping <f>.
##  The parameter <val> can either specify the length of the sequence to
##  be computed or be a `stopping value' such that the function stops when
##  it reaches some iterate <n>^(<f>^<k>) = <val>, depending on whether
##  <cond> = `"length"' or <cond> = `"stop"'.
##
DeclareGlobalFunction( "Trajectory" );

#############################################################################
##
#F  TrajectoryModulo( <f>, <n>, <m>, <lng> ) . .  trajectory (mod <m>) of <f>
#F  TrajectoryModulo( <f>, <n>, <lng> )
##
##  Returns the sequence $(n_i), i = 0, \dots, lng-1$ with $n_i := n^(f^i)$
##  mod <m> as a list. If <m> is not given, it defaults to the modulus
##  of <f>.
##
DeclareGlobalFunction( "TrajectoryModulo" );

#############################################################################
##
#F  CoefficientsOnTrajectory( <f>, <n>, <val>, <cond>, <all> )
##
##  This function computes accumulated coefficients on the trajectory of <n>
##  under the rcwa mapping <f>. More precisely: it computes a list <c> of
##  coefficient triples such that for any <k>, we have
##  <n>^(<f>^(<k>-1)) = (<c>[<k>][1]*<n> + <c>[<k>][2])/<c>[<k>][3].
##  The meaning of the arguments <val> and <cond> is the same as in
##  `Trajectory'; if <all> = `true', the whole sequence of coefficient
##  triples is returned, otherwise the result is only the last triple.
##
DeclareGlobalFunction( "CoefficientsOnTrajectory" );

#############################################################################
##
#O  ShortCycles( <f>, <maxlng> ) . . . . short cycles of the rcwa mapping <f>
##
##  Computes all ``single'' finite cycles of the rcwa mapping <f>
##  of length <= <maxlng>.
##
DeclareOperation( "ShortCycles", [ IsRcwaMapping, IsPosInt ] );

#############################################################################
##
#A  CycleType( <f> ) . . . . . . . . . . . . . . . . . . .  cycle type of <f>
##
##  The *cycle type* of a tame rcwa mapping <f> is denoted by a list of two
##  lists, where the first list is the set of the cycle lengths which occur
##  infinitely often, and the second list contains the cycle lengths which
##  occur only finitely often, with the respective multiplicities and sorted
##  by increasing length.
##
DeclareAttribute( "CycleType", IsRcwaMapping );

#############################################################################
##
#A  RespectedClassPartition( <sigma> ) . . . . . .  respected class partition
##
##  A partition of the base ring <R> into a finite number of residue classes,
##  on which the bijective mapping <sigma> acts as a permutation. 
##  The partition is non-trivial as long as Modulus( <sigma> ) <> One( <R> ).
##  Such a partition exists always if <sigma> is tame and <R> has the
##  `class halving property'. 
##
DeclareAttribute( "RespectedClassPartition", IsRcwaMapping );

#############################################################################
##
#O  CompatibleConjugate( <g>, <h> ) . . . . . . . . . .  compatible conjugate
##
##  Computes some mapping <h>^<r> such that there is a partition which is
##  respected by both <g> and <h>^<r>, hence such that the group generated
##  by <g> and <h>^<r> is tame. Methods may return any such mapping.
##
DeclareOperation( "CompatibleConjugate", [ IsRcwaMapping, IsRcwaMapping ] );

#############################################################################
##
#O  ContractionCentre( <f>, <maxn>, <bound> ) . . . . . .  contraction centre
##
##  Tries to compute the *contraction centre* of the rcwa mapping <f> --
##  assuming its existence this is the uniquely-defined finite subset $S_0$
##  of the base ring <R> which is mapped bijectively onto itself under <f>
##  and where for any $x \in R$ there is an integer $k$ such that
##  $x^{f^k} \in S_0$. The mapping <f> is assumed to be contracting.
##  As this problem seems to be computationally undecidable methods will be
##  probabilistic. The argument <maxn> is a bound on the starting value
##  and <bound> is a bound on the elements of the sequence to be searched.
##  If the limit <bound> is exceeded, an Info message on some Info level
##  of InfoRCWA is given.
##
DeclareOperation( "ContractionCentre",
                  [ IsRcwaMapping, IsRingElement, IsPosInt ] );
DeclareSynonym( "ContractionCenter", ContractionCentre );

#############################################################################
##
#A  Divergence( <f> ) . . . . . . . . . . . . . . . . . . . divergence of <f>
##
##  The divergence of the rcwa mapping <f>.
##  This is conjectured to be a measure for how fast an rcwa mapping
##  contracts (if its divergence is smaller than 1) or how fast its
##  trajectories diverge (if its divergence is larger than 1).
##
DeclareAttribute( "Divergence", IsRcwaMapping );

#############################################################################
##
#A  ImageDensity( <f> ) . . . . . . . . . . . . . . . .  image density of <f>
##
##  The image density of the rcwa mapping <f>.
##  The *image density* of an rcwa mapping measures how ``dense'' its image
##  is -- an image density > 1 implies that there have to be ``overlaps'',
##  i.e. that the mapping cannot be injective, a surjective mapping always
##  has image density \ge 1, and the image density of a bijective mapping
##  is equal to 1.
##
DeclareAttribute( "ImageDensity", IsRcwaMapping );

#############################################################################
##
#O  Restriction( <g>, <f> ) . . . . . . . . . . . . restriction of <g> by <f>
##
##  Computes the restriction of the rcwa mapping <g> by (i.e. to the image
##  of) the rcwa mapping <f>.
##
DeclareOperation( "Restriction",
                  [ IsRcwaMapping, IsRcwaMapping ] );

#############################################################################
##
#E  rcwamap.gd . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
