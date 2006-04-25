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
##  $a_{r(m)}, b_{r(m)}, c_{r(m)} \in R$ such that the restriction of $f$
##  to the set $r(m) = \{r + km | k \in R\}$ is given by
##  $$
##    n \ \mapsto \ \frac{a_{r(m)} \cdot n + b_{r(m)}}{c_{r(m)}}.
##  $$
##  We always assume that $c_{r(m)} > 0$, that all fractions are reduced,
##  i.e. that $\gcd( a_{r(m)}, b_{r(m)}, c_{r(m)} ) = 1$, and that $m$ is
##  chosen multiplicatively minimal. Apart from the restrictions imposed by
##  the condition that the image of any residue class $r(m)$ under $f$ must
##  be a subset of $R$ and that we cannot divide by 0, the coefficients
##  $a_{r(m)}$, $b_{r(m)}$ and $c_{r(m)}$ can be any ring elements.
##  We call $m$ the *modulus* of $f$. By *products* of rcwa mappings we
##  always mean their compositions as mappings, and by the *inverse* of
##  a bijective rcwa mapping we mean its inverse mapping. 
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
##    <Modulus>& The modulus $m$ is stored as a component <modulus> in any
##    rcwa mapping object. 
##
##    <Coefficients>& The list of coefficients is stored as a component
##    <coeffs> in any rcwa mapping object. The component <coeffs> is a list
##    of $|R/mR|$ lists of three elements of $R$, each, giving
##    the coefficients $a_{r(m)}$, $b_{r(m)}$ and $c_{r(m)}$ for $r(m)$
##    running through all residue classes (mod $m$). The ordering of
##    these triples is defined by the ordering of the residues $r$ mod $m$
##    in `AllResidues( <R>, <m> )'.
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
#C  IsRcwaMappingOfZ . . . . . . . . . . . . . . . . . . . rcwa mappings of Z
##
##  The category of all rcwa mappings of $\Z$.
##
DeclareCategory( "IsRcwaMappingOfZ", IsRingElement );

#############################################################################
##
#C  IsRcwaMappingOfZ_pi . . . . . . . . . . . . . . . rcwa mappings of Z_(pi)
##
##  The category of all rcwa mappings of semilocalizations of $\Z$.
##
DeclareCategory( "IsRcwaMappingOfZ_pi", IsRingElement );

#############################################################################
##
#C  IsRcwaMappingOfZOrZ_pi . . . . . . . . . . . rcwa mappings of Z or Z_(pi)
##
##  The category of all rcwa mappings of the ring $\Z$ or semilocalizations
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
##  Family of rcwa mappings with underlying ring $\Z_{(\pi)}$, where the set
##  $\pi$ is given by the list <primes>.
##
DeclareGlobalFunction( "RcwaMappingsOfZ_piFamily" );

#############################################################################
##
#F  RcwaMappingsOfGFqxFamily( <R> ) . family of rcwa mappings of R = GF(q)[x]
##
##  Family of rcwa mappings of $R$ = GF($q$)[$x$].
##
DeclareGlobalFunction( "RcwaMappingsOfGFqxFamily" );

#############################################################################
##
#R  IsRcwaMappingStandardRep . . . "standard" representation of rcwa mappings
##
##  Representation of rcwa mappings by modulus <modulus> (in the following
##  denoted by $m$) and coefficient list <coeffs>.
##
##  The component <coeffs> is a list of $|R/mR|$ lists of three elements of
##  the underlying ring $R$, each, giving the coefficients $a_{r(m)}$,
##  $b_{r(m)}$ and $c_{r(m)}$ for $r(m)$ running through all residue classes
##  (mod $m$).
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
#F  LocalizedRcwaMapping( <f>, <p> )
#F  SemilocalizedRcwaMapping( <f>, <pi> )
##
##  These functions return the rcwa mapping of $\Z_{(p)}$ resp. $\Z_{(\pi)}$
##  with the same coefficients as <f>.
##
DeclareGlobalFunction( "LocalizedRcwaMapping" );
DeclareGlobalFunction( "SemilocalizedRcwaMapping" );

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
#F  PrimeSwitch( <p> ) .  rcwa mapping of Z with multiplier <p> and divisor 2
#F  PrimeSwitch( <p>, <k> )
#P  IsPrimeSwitch( <sigma> )
##
DeclareGlobalFunction( "PrimeSwitch" );
DeclareProperty( "IsPrimeSwitch", IsRcwaMapping );

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
#F  mKnot( <m> ) . . . . . . . . . . rcwa mapping of Timothy P. Keller's type
##
##  Given an odd integer <m>, this function returns the bijective rcwa
##  mapping $g_m$ as defined in
##
##  Timothy P. Keller. Finite Cycles of Certain Periodically Linear
##  Permutations. Missouri J. Math. Sci. 11(1999), no. 3, 152-157.
##
DeclareGlobalFunction( "mKnot" );

#############################################################################
##
#F  ClassUnionShift( <S> ) . . . . . shift of rc.-union <S> by Modulus( <S> )
##
##  The rcwa mapping which maps <S> to <S> + `Modulus'(<S>) and fixes the
##  complement of <S>.
##
DeclareGlobalFunction( "ClassUnionShift" );

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
#A  Support( <G>|<g> )  support (moved points) of perm.-group <G> / perm. <g>
##  
DeclareAttribute( "Support", IsGroup );

#############################################################################
##
#A  Multiplier( <f> ) . . . . . . . .  the multiplier of the rcwa mapping <f>
##
##  We define the *multiplier* of an rcwa mapping <f> by the standard
##  associate of the least common multiple of the coefficients $a_{r(m)}$.
##
DeclareAttribute( "Multiplier", IsRcwaMapping );
DeclareSynonym( "Mult", Multiplier );

#############################################################################
##
#A  Divisor( <f> ) . . . . . . . . . . .  the divisor of the rcwa mapping <f>
##
##  We define the *divisor* of an rcwa mapping <f> by the standard
##  associate of the least common multiple of the coefficients $c_{r(m)}$.
##
DeclareAttribute( "Divisor", IsRcwaMapping );
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
##  equal to 1.
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
##  Indicates whether or not the rcwa mapping <f> of $\Z$ or $\Z_{\pi}$ is
##  class-wise order-preserving.
##
DeclareProperty( "IsClassWiseOrderPreserving", IsRcwaMappingOfZOrZ_pi ); 

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
#A  Sign( <f> ) . . . . . . . . . . . . the sign of the rcwa mapping <f> of Z
##
##  The *sign* of the rcwa mapping <f>. The sign mapping is an epimorphism
##  from RCWA($\Z$) to U($\Z$).
##
DeclareAttribute( "Sign", IsRcwaMapping );

#############################################################################
##
#O  Multpk( <f>, <p>, <k> )  the elements multiplied by a multiple of <p>^<k>
##
##  The set of elements $n$ of the base ring $R$ which <f> maps to
##  $(a_{r(m)} n + b_{r(m)})/c_{r(m)}$, where $p^k||a_{r(m)}$ if $k \gt 0$,
##  resp. $p^{-k}||c_{r(m)}$ if $k \lt 0$ resp. $p \nmid a_{r(m)}, c_{r(m)}$
##  if $k = 0$.
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
#A  Sources
#A  Sinks
#A  Loops
##
##  Let <f> be an rcwa mapping with modulus <m>. Then, `Sources(<f>)' and
##  `Sinks(<f>)' are lists of unions of residue classes (mod <m>), and
##  `Loops(<f>)' is a list of residue classes (mod <m>).
##
##  The list `Sources(<f>)' contains an entry for any strongly connected
##  component of the transition graph of <f> for modulus <m> which has only
##  outgoing edges. The list entry corresponding to a given such strongly
##  connected component is just the union of its vertices. The description of
##  the list `Sinks(<f>)' is obtained by replacing "outgoing" by "ingoing".
##
##  The entries of the list `Loops(<f>)' are the residue classes (mod <m>)
##  which are not setwisely fixed by <f>, but which intersect nontrivially
##  with their images under <f>.
##
DeclareAttribute( "Sources", IsRcwaMapping );
DeclareAttribute( "Sinks", IsRcwaMapping );
DeclareAttribute( "Loops", IsRcwaMapping );

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
##  it computes the part of the trajectory of <f> starting at <n> which ends
##  at the first occurence of an iterate in the set <terminal>. In place of
##  the ring element <n>, a finite set of ring elements or a union of residue
##  classes can be given. In the second and fifth case the iterates are
##  reduced (mod <m>) to save memory.
##
##  In the third and sixth case the operation computes "accumulated coeffi-
##  cients" on the trajectory of <n> under the rcwa mapping <f>. The term
##  "accumulated coefficients" denotes the list <c> of coefficient triples
##  such that for any <k> we have <n>^(<f>^(<k>-1)) = (<c>[<k>][1]*<n> +
##  <c>[<k>][2])/<c>[<k>][3]. The argument <whichcoeffs> can either be
##  "AllCoeffs" or "LastCoeffs", and determines whether the whole list of
##  triples or only the last triple is computed.
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
##           unions of the returned sets of residue classes!
##
DeclareGlobalFunction( "TraceTrajectoriesOfClasses" );

#############################################################################
##
#F  SearchCycle( <l> ) . . . . . . . . . . . . a simple-minded cycle detector
##
DeclareGlobalFunction( "SearchCycle" );

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
#A  RespectedPartition( <sigma> ) . . . . . . . . . . . . respected partition
##
##  A partition of the base ring <R> into a finite number of residue classes,
##  on which the bijective rcwa mapping <sigma> acts as a permutation, and on
##  those elements <sigma> is affine. Provided that <R> has a residue class
##  ring of cardinality 2, such a partition exists if and only if <sigma> is
##  tame.
##
DeclareAttribute( "RespectedPartition", IsRcwaMapping );

#############################################################################
##
#O  PermutationOpNC( <sigma>, <P>, <act> )
##
DeclareOperation( "PermutationOpNC",
                  [ IsObject, IsListOrCollection, IsFunction ] );

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
##  The coarsest partition of the base ring <R> on whose elements the rcwa
##  mapping <f> is affine.
##
DeclareAttribute( "LargestSourcesOfAffineMappings", IsRcwaMapping );

#############################################################################
##
#F  IncreasingOn( <f> ) . . . . . . . . . . . set of n such that |n^f| >> |n|
##
##  The union of all residue classes $r(m)$ such that
##  $|R/a_{r(m)}R|>|R/c_{r(m)}R|$, where $R$ denotes the source of <f>
##  and $m$ denotes the modulus of <f>.
##
DeclareGlobalFunction( "IncreasingOn" );

#############################################################################
##
#F  DecreasingOn( <f> ) . . . . . . . . . . . set of n such that |n^f| << |n|
##
##  The union of all residue classes $r(m)$ such that
##  $|R/a_{r(m)}R|<|R/c_{r(m)}R|$, where $R$ denotes the source of <f>
##  and $m$ denotes the modulus of <f>.
##
DeclareGlobalFunction( "DecreasingOn" );

#############################################################################
##
#O  LikelyContractionCentre( <f>, <maxn>, <bound> ) likely contraction centre
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
DeclareOperation( "LikelyContractionCentre",
                  [ IsRcwaMapping, IsRingElement, IsPosInt ] );
DeclareSynonym( "LikelyContractionCenter", LikelyContractionCentre );

#############################################################################
##
#O  GuessedDivergence( <f> ) . . . . . . . . . . .  guessed divergence of <f>
##
##  Guesses the "divergence" of the rcwa mapping <f>.
##  This is conjectured to be a measure for how fast an rcwa mapping
##  contracts (if its divergence is smaller than 1) or how fast its
##  trajectories diverge (if its divergence is larger than 1).
##
DeclareOperation( "GuessedDivergence", [ IsRcwaMapping ] );

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
#F  InjectiveAsMappingFrom( <f> ) . . . .  some set on which <f> is injective
##
##  Returns some subset <S> of `Source'(<f>) such that the restriction of <f>
##  to <S> is injective.
##
DeclareGlobalFunction( "InjectiveAsMappingFrom" );

#############################################################################
##
#A  RightInverse( <f> ) . . . . . . . . . . . . . . . .  right inverse of <f>
##
##  The right inverse of <f>, i.e. a mapping <g> such that $fg = 1$.
##  The mapping <f> must be injective.
##
DeclareAttribute( "RightInverse", IsRcwaMapping );

#############################################################################
##
#O  CommonRightInverse( <l>, <r> ) . . . . .  mapping <d> s.th. $ld = rd = 1$
##
##  Returns a mapping <d> such that $ld = rd = 1$.
##  The mappings <l> and <r> must be injective, and their images must form
##  a partition of the underlying ring.
##
DeclareOperation( "CommonRightInverse", [ IsRcwaMapping, IsRcwaMapping ] );

#############################################################################
##
#O  Restriction( <g>, <f> ) . . . . . . . . . . . . restriction of <g> by <f>
##
##  Computes the *restriction* of the rcwa mapping <g> by (i.e. to the image
##  of) the rcwa mapping <f>. The mapping <f> must be injective.
##
DeclareOperation( "Restriction", [ IsRcwaMapping, IsRcwaMapping ] );

#############################################################################
##
#O  Induction( <g>, <f> ) . . . . . . . . . . . . . . induction of <g> by <f>
##
##  Computes the *induction* of the rcwa mapping <g> by the rcwa mapping <f>.
##  The mapping <f> must be injective, and both the support of <g> and its
##  image under <g> must lie in the image of <f>.
##  It holds `Induction( Restriction( <g>, <f> ), <f> ) = <g>',
##  thus induction is the one-sided inverse operation of restriction.
##
DeclareOperation( "Induction", [ IsRcwaMapping, IsRcwaMapping ] );

#############################################################################
##
#A  LaTeXName( obj ) . . . . . . . . . . . . .  LaTeX string for object <obj>
##
DeclareAttribute( "LaTeXName", IsObject );

#############################################################################
##
#E  rcwamap.gd . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here