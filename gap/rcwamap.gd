#############################################################################
##
#W  rcwamap.gd                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains declarations of functions, operations etc. for
##  computing with residue class-wise affine mappings.
##
Revision.rcwamap_gd :=
  "@(#)$Id$";

#############################################################################
##
#V  RcwaInfo . . . . . . . . . . . . . . . . . .  info class for RCWA package
##
##  This is the Info class of the RCWA package (see~"ref:Info Functions" 
##  in the {\GAP} Reference Manual for a description of the Info mechanism).
##
DeclareInfoClass( "RcwaInfo" );

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
#V  IntegralRcwaMappingsFamily . . . the family of all integral rcwa mappings
##
DeclareGlobalVariable( "IntegralRcwaMappingsFamily" );

#############################################################################
##
#F  SemilocalIntegralRcwaMappingsFamily( <primes> )
##
##  Family of semilocal integral rcwa mappings with underlying ring $\Z_\pi$,
##  where the set $\pi$ is given by the list <primes>.
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
#F  AllGFqPolynomialsModDegree( <q>, <d>, <x> ) . residues in canonical order
##
##  Returns a sorted list of all residues modulo a polynomial of degree <d>
##  over GF(<q>) in the variable <x>.
##  This gives also the ordering in which the coefficients of a modular rcwa
##  mapping are stored; thus, if <f> is a modular rcwa mapping over
##  GF(<q>)[x] with coefficients list <c>, whose modulus <m> has degree <d>,
##  then <f> maps a polynomial <P> with <P> mod <m> = <r> to
##
##  ( <c>[`Position'(<res>,<r>)][1] * <P> + <c>[`Position'(<res>,<r>)][2] ) /
##    <c>[`Position'(<res>,<r>)][3],
##
##  where <res> denotes the list of residues returned by this function.
##
DeclareGlobalFunction( "AllGFqPolynomialsModDegree" );

#############################################################################
##
#F  UnderlyingRing( <fam> ) . . . . . . . . . . . . . . . . . underlying ring
##
##  The underlying ring of a family of rcwa mappings.
##
DeclareAttribute( "UnderlyingRing", IsObject );

#############################################################################
##
#F  UnderlyingIndeterminate( <fam> ) . . indet. of underlying polynomial ring
##
##  The indeterminate of the underlying polynomial ring of the family <fam>
##  of modular rcwa mappings.
##
DeclareAttribute( "UnderlyingIndeterminate", IsFamily );

#############################################################################
##
#R  IsRationalBasedRcwaDenseRep . ."dense" rep. of "rat.-based" rcwa mappings
##
##  Representation of integral rcwa mappings and semilocal integral rcwa
##  mappings by modulus <modulus> and coefficient list <coeffs>.
##
##  The coefficient list is a list of <modulus> lists of 3 integers,
##  defining the mapping on the residue classes
##  0 .. <modulus> - 1 (mod <modulus>), in this order. 
##  If <n> mod <modulus> = <r>, then <n> is mapped to
##  (<coeffs>[<r>+1][1] * <n> + <coeffs>[<r>+1][2])/<coeffs>[<r>+1][3].
##
DeclareRepresentation( "IsRationalBasedRcwaDenseRep", 
                       IsComponentObjectRep and IsAttributeStoringRep, 
                       [ "modulus", "coeffs" ] );

#############################################################################
##
#R  IsModularRcwaDenseRep . .`dense' representation of integral rcwa mappings
##
##  Representation of modular rcwa mappings by finite field size <q>,
##  modulus <modulus> and coefficient list <coeffs>.
##
##  The coefficient list is a list of <q>^<d> lists of 3 polynomials,
##  where <d> denotes the degree of <modulus>, defining the mapping on the
##  residue classes (mod <modulus>), in `natural' order. 
##  If <P> mod <modulus> = <r>, then <P> is mapped to
##  (<coeffs>[<pos(r)>][1]*<P>+<coeffs>[<pos(r)>][2])/<coeffs>[<pos(r)>][3],
##  where <pos(r)> denotes the position of <r> in the sorted list of
##  polynomials of degree less than <d> over GF(<q>).
##
DeclareRepresentation( "IsModularRcwaDenseRep", 
                       IsComponentObjectRep and IsAttributeStoringRep, 
                       [ "modulus", "coeffs" ] );

#############################################################################
##
#F  IntegralRcwaMapping( <coeffs> )
#F  IntegralRcwaMapping( <perm>, <range> )
#F  IntegralRcwaMapping( <modulus>, <val> )
#F  IntegralRcwaMappingNC( <coeffs> )
#F  IntegralRcwaMappingNC( <perm>, <range> )
#F  IntegralRcwaMappingNC( <modulus>, <val> )
##
##  Construction of the integral rcwa mapping 
##
##  \beginlist
##  \item{(a)}
##    with coefficients <coeffs> resp.
##  \item{(b)}
##    acting on the translates of <range> by integral multiples
##    of the length of <range> as the translates of the finite permutation
##    <perm> to the respective intervals resp.
##  \item{(c)}
##    with modulus <modulus> with values prescribed by the list <val>, which
##    consists of 2 * <modulus> pairs giving preimage and image for 2 points
##    per residue class (mod <modulus>).
##  \endlist
##
##  The difference between `IntegralRcwaMapping' and `IntegralRcwaMappingNC'
##  is that the former performs some argument checks which are omitted in the
##  latter, where just anything may happen if wrong or inconsistent arguments
##  are given.
##
DeclareGlobalFunction( "IntegralRcwaMapping" );
DeclareGlobalFunction( "IntegralRcwaMappingNC" );

#############################################################################
##
#F  SemilocalIntegralRcwaMapping( <fam>, <coeffs> )
#F  SemilocalIntegralRcwaMappingNC( <fam>, <coeffs> )
##
##  Construction of the semilocal integral rcwa mapping with coefficients
##  <coeffs> in the family <fam>.
##
##  The difference between `SemilocalIntegralRcwaMapping' and
##  `SemilocalIntegralRcwaMappingNC' is that the former performs some
##  argument checks which are omitted in the latter, where just anything may
##  happen if wrong or inconsistent arguments are given.
##
DeclareGlobalFunction( "SemilocalIntegralRcwaMapping" );
DeclareGlobalFunction( "SemilocalIntegralRcwaMappingNC" );

#############################################################################
##
#F  ModularRcwaMapping( <fam>, <modulus>, <coeffs> )
#F  ModularRcwaMappingNC( <fam>, <modulus>, <coeffs> )
##
##  Construction of the modular rcwa mapping with modulus <modulus> and
##  coefficients <coeffs> in the family <fam>.
##
##  The difference between `ModularRcwaMapping' and `ModularRcwaMappingNC'
##  is that the former performs some argument checks which are omitted in the
##  latter, where just anything may happen if wrong or inconsistent arguments
##  are given.
##
DeclareGlobalFunction( "ModularRcwaMapping" );
DeclareGlobalFunction( "ModularRcwaMappingNC" );

#############################################################################
##
#F  RcwaMapping( <coeffs> )
#F  RcwaMapping( <perm>, <range> )
#F  RcwaMapping( <modulus>, <val> )
#F  RcwaMapping( <fam>, <coeffs> )
#F  RcwaMapping( <fam>, <modulus>, <coeffs> )
##
##  Shorthand for `IntegralRcwaMapping' (first 3 cases),
##  `SemilocalIntegralRcwaMapping' (4th case) resp.
##  `ModularRcwaMapping' (last case).
##
DeclareGlobalFunction( "RcwaMapping" );

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
#O  Modulus( <f> ) . . . . . . . . . . . . .  modulus of the rcwa mapping <f>
##
DeclareOperation( "Modulus", [ IsRcwaMapping ] );

############################################################################# 
## 
#A  Multiplier( <f> ) . . . . . . . .  the multiplier of the rcwa mapping <f> 
## 
##  We define the *multiplier* of an rcwa mapping <f> as the standard
##  associate of the least common multiple of the coefficients $a_r$
##  (cp. chapter `introduction' in the manual).
## 
DeclareAttribute( "Multiplier", IsRcwaMapping ); 

############################################################################# 
## 
#A  Divisor( <f> ) . . . . . . . . . . .  the divisor of the rcwa mapping <f> 
## 
##  We define the *divisor* of an rcwa mapping <f> as the standard
##  associate of the least common multiple of the coefficients $c_r$
##  (cp. chapter `introduction' in the manual).
## 
DeclareAttribute( "Divisor", IsRcwaMapping ); 

############################################################################# 
## 
#P  IsFlat( <f> ) . . . . indicates whether or not <f> is a flat rcwa mapping 
## 
##  We say that an rcwa mapping is *flat* if and only if its multiplier
##  and its divisor are equal to 1.
##
DeclareProperty( "IsFlat", IsRcwaMapping ); 

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
#O  RcwaGraph( <f> ) . . . . . . . . . . . . .  graph of the rcwa mapping <f>
##
##  Graph associated to rcwa mapping <f>.
##
##  We define the *graph* $\Gamma_f$ associated
##  to an rcwa mapping $f$ with modulus $m$ as follows:
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
##  This requires the package `grape' to be loaded.
##
DeclareOperation( "RcwaGraph", [ IsRcwaMapping ] );
if   TestPackageAvailability( "grape", "4.0" ) = fail
then Graph := ReturnFail; fi;

############################################################################# 
##
#F  TransitionMatrix( <f>, <deg> ) . . <deg>x<deg>-`Transition matrix' of <f>
##
##  We define the *transition matrix* <M> of degree <deg> of the rcwa mapping
##  <f> by <M>[<i>+1][<j>+1] = 1 if there is an <n> congruent to <i> (mod
##  <deg>) such that <n>^<f> is congruent to <j> mod <deg>, and 0 if not.
##  Their rank (and in case it is invertible the absolute value of its 
##  determinant) does not depend on the particular assignment of the residue
##  classes (mod <deg>) to rows / columns.
##
DeclareGlobalFunction( "TransitionMatrix" );

#############################################################################
##
#A  PrimeSet( <f> ) . . . . . . . . . . . . prime set of the rcwa mapping <f>
##
##  Prime set of rcwa mapping <f>.
##
##  We define the prime set of an rcwa mapping <f> as the set of all primes
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
#A  StandardConjugate( <f> ) . .  standard rep. of the conjugacy class of <f>
##
##  Some ``nice'' canonical representative of the conjugacy class of the
##  bijective integral rcwa mapping <f> in the whole group RCWA(Z).
##  Two integral rcwa mappings are conjugate if and only if their 
##  ``standard conjugates'' are equal. 
##
DeclareAttribute( "StandardConjugate", IsRcwaMapping ); 

#############################################################################
##
#A  StandardizingConjugator( <f> ) . . mapping <x>, s.th. <f>^<x> is standard
##
##  A mapping <x>, such that <f>^<x> is the ``standard'' representative of
##  the conjugacy class of the bijective integral rcwa mapping <f> in the
##  whole group RCWA(Z).
##
DeclareAttribute( "StandardizingConjugator", IsRcwaMapping );

#############################################################################
##
#E  rcwamap.gd . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here