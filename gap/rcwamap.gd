#############################################################################
##
#W  rcwamap.gd                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains declarations of functions, operations etc. for
##  computing with integral residue class-wise affine mappings.
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
#C  IsIntegralRcwaMapping . . . . . . . . . . . . . .  integral rcwa mappings
#C  IsRcwaMapping 
##
##  The category of all integral rcwa mappings.
##
##  The version `IsRcwaMapping' is reserved as a term for denoting any kind
##  of rcwa mappings, if in future versions also rcwa mappings over other
##  PID's will be implemented.
##
DeclareCategory( "IsIntegralRcwaMapping", IsRingElement );
DeclareSynonym( "IsRcwaMapping", IsIntegralRcwaMapping );

#############################################################################
##
#V  IntegralRcwaMappingsFamily . . . the family of all integral rcwa mappings
##
DeclareGlobalVariable( "IntegralRcwaMappingsFamily" );

#############################################################################
##
#R  IsIntegralRcwaDenseRep . `dense' representation of integral rcwa mappings
##
##  Representation of integral rcwa mappings by coefficient list <coeffs>
##  and modulus <modulus>.
##
##  The coefficient list is a list of <modulus> lists of 3 integers,
##  defining the mapping on the residue classes
##  0 .. <modulus> - 1 (mod <modulus>), in this order. 
##  If <n> mod <modulus> = <r>, then <n> is mapped to
##  (<coeffs>[<r>+1][1] * <n> + <coeffs>[<r>+1][2])/<coeffs>[<r>+1][3].
##
DeclareRepresentation( "IsIntegralRcwaDenseRep", 
                       IsComponentObjectRep and IsAttributeStoringRep, 
                       [ "coeffs", "modulus" ] );

#############################################################################
##
#F  IntegralRcwaMapping( <coeffs> )
#F  IntegralRcwaMapping( <perm>, <range> )
#F  IntegralRcwaMapping( <modulus>, <val> )
#F  RcwaMapping( <coeffs> )
#F  RcwaMapping( <perm>, <range> )
#F  RcwaMapping( <modulus>, <val> )
##
##  Construction of the rcwa mapping 
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
DeclareGlobalFunction( "IntegralRcwaMapping" );
DeclareSynonym( "RcwaMapping", IntegralRcwaMapping );

#############################################################################
##
#V  ZeroIntegralRcwaMapping . . . . . . . . . . .  zero integral rcwa mapping
##
DeclareGlobalVariable( "ZeroIntegralRcwaMapping" );

#############################################################################
##
#V  IdentityIntegralRcwaMapping . . . . . . . identity integral rcwa mapping
##
DeclareGlobalVariable( "IdentityIntegralRcwaMapping" );

#############################################################################
##
#O  Modulus( <f> ) . . . . . . . . . . . . .  modulus of the rcwa mapping <f>
##
DeclareOperation( "Modulus", [ IsRcwaMapping ] );

#############################################################################
##
#A  ModulusOfRcwaMapping( <f> ) . . . . . . . modulus of the rcwa mapping <f>
##
DeclareAttribute( "ModulusOfRcwaMapping", IsRcwaMapping );

#############################################################################
##
#A  CoefficientsOfRcwaMapping( <f> ) . . coefficients of the rcwa mapping <f>
##
DeclareAttribute( "CoefficientsOfRcwaMapping", IsRcwaMapping );

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
##  Indicates whether or not the integral rcwa mapping <f> is class-wise
##  order-preserving.
##
DeclareProperty( "IsClassWiseOrderPreserving", IsIntegralRcwaMapping ); 

#############################################################################
##
#O  RcwaGraphAdjacencyMatrix( <f> ) . . . .  adjacency matrix of graph of <f> 
##
##  Computes the weighted adjacency matrix of the graph of the
##  rcwa mapping <f> (see `RcwaGraph' below).
##
DeclareOperation( "RcwaGraphAdjacencyMatrix", [ IsRcwaMapping ] );

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
if   TestPackageAvailability( "grape", "4.0" ) <> true
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
#O  Variation( <f> ) . . . . . . . variation of the integral rcwa mapping <f>
##
##  We define the variation of an integral rcwa mapping <f> as
##  $$
##    \lim_{n \rightarrow \infty} \
##    \frac{1}{2n^2} \sum_{i=-n}^{n-1} \left| i^f - (i+1)^f \right|.
##  $$
##  The variation is some kind of measure for how much the mapping <f> is
##  `oscillating'. It can be computed easily from the coefficients.
##
DeclareOperation( "Variation", [ IsIntegralRcwaMapping ] );

#############################################################################
##
#E  rcwamap.gd . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here