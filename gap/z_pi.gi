#############################################################################
##
#W  z_pi.gi                  GAP4 Package `RCWA'                  Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains implementations of methods for computing with the
##  semilocalizations Z_pi of the ring of integers.
##
Revision.z_pi_gi :=
  "@(#)$Id$";

#############################################################################
##
#M  Z_piCons( <filter>, <pi> ) . . . . . . . . . . . . . . . . . . . . . Z_pi
##
##  Semilocalization Z_pi of the ring of integers, for prime set <pi>.
##
InstallMethod( Z_piCons, "natural Z_pi", true, 
               [ IsRing, IsList ], 0,

  function ( filter, pi )

    local  R;

    R := Objectify( NewType( FamilyObj( Integers ),
                             IsRing and IsAttributeStoringRep ),
                    rec( primes := Immutable( pi ) ) );
    SetIsTrivial( R, false );
    SetIsZ_pi( R, true );
    SetZero( R, 0 ); SetOne( R, 1 );
    SetIsFinite( R, false ); SetSize( R, infinity );
    SetIsAssociative( R, true ); SetIsCommutative( R, true );
    SetRepresentative( R, 1/Minimum(Difference(List(pi,NextPrimeInt),pi)) );
    SetElementsFamily( R, FamilyObj( 1 ) );
    SetNoninvertiblePrimes( R, R!.primes );
    SetName( R, Concatenation( "Z_", String(pi) ) );
    return R;
  end );

#############################################################################
##
#F  Z_pi( <pi> ) . . . . . . . . . . semilocalization Z_pi for prime set <pi>
##
InstallGlobalFunction( Z_pi, 

  function ( pi )

    if not ForAll(pi,IsPrimeInt)
    then Error("Z_pi( <pi> ): <pi> must be a set of primes.\n"); fi;
    return Z_piCons( IsRing, Set( pi ) );
  end );

#############################################################################
##
#M  String( <R> ) . . . . . . . . . . . . . . . . . . . . . . . . .  for Z_pi
##
InstallMethod( String,
               "for Z_pi", ReturnTrue, [ IsZ_pi ], 0, R -> Name( R ) );

#############################################################################
##
#M  \=( <R>, <S> ) . . . . . . . . . . . . . . . . . . . . . . . . for Z_pi's
##
InstallMethod( \=,
               "for Z_pi's", ReturnTrue, [ IsZ_pi, IsZ_pi ], 0,

  function ( R, S ) return R!.primes = S!.primes; end );

#############################################################################
##
#M  \in( <x>, <R> ) . . . . . . . . . . . . . . . . . . . for object and Z_pi
##
InstallMethod( \in,
               "for object and Z_pi", ReturnTrue,
               [ IsObject, IsZ_pi ], 0,

  function ( x, R )

    if not IsRat(x) then return false; fi;
    return Intersection(Set(Factors(DenominatorRat(x))),R!.primes) = [];
  end );

#############################################################################
##
#M  Intersection2( <R>, <S> ) . . . . . . . . . . . . . . . . . .  for Z_pi's
##
InstallMethod( Intersection2,
               "for Z_pi's", ReturnTrue, [ IsZ_pi, IsZ_pi ], 0,

  function ( R, S )

    return Z_pi( Union( R!.primes, S!.primes ) );
  end );

#############################################################################
##
#M  Intersection2( Rationals, <R> ) . . . . . . . . .  for Rationals and Z_pi
##
InstallMethod( Intersection2,
               "for Rationals and Z_pi", ReturnTrue,
               [ IsRationals, IsZ_pi ], 0,
  function ( Rat, R ) return R; end );

#############################################################################
##
#M  Intersection2( <R>, Rationals ) . . . . . . . . .  for Z_pi and Rationals
##
InstallMethod( Intersection2,
               "for Z_pi and Rationals", ReturnTrue,
               [ IsZ_pi, IsRationals ], 0,
  function ( R, Rat ) return R; end );

#############################################################################
##
#M  IsSubset( <R>, <S> ) . . . . . . . . . . . . . . . . . . . . . for Z_pi's
##
InstallMethod( IsSubset,
               "for Z_pi's", ReturnTrue, [ IsZ_pi, IsZ_pi ], 0,

  function ( R, S ) return IsSubset( S!.primes, R!.primes ); end );

#############################################################################
##
#M  IsSubset( Rationals, <R> ) . . . . . . . . . . . . for Rationals and Z_pi
##
InstallMethod( IsSubset,
               "for Rationals and Z_pi", ReturnTrue,
               [ IsRationals, IsZ_pi ], 0, ReturnTrue );

#############################################################################
##
#M  IsSubset( <R>, Integers ) . . . . . . . . . . . . . for Z_pi and Integers
##
InstallMethod( IsSubset,
               "for Z_pi and Integers", ReturnTrue,
               [ IsZ_pi, IsIntegers ], 0, ReturnTrue );

#############################################################################
##
#M  StandardAssociate( <R>, <x> ) . . . . . . .  for Z_pi and element thereof
##
InstallMethod( StandardAssociate,
               "for Z_pi and element thereof", ReturnTrue,
               [ IsZ_pi, IsRat ], 0,

  function ( R, x )

    local  pi;

    if not x in R then return fail; fi; if x = 0 then return 0; fi;
    pi := NoninvertiblePrimes( R );
    return Product( Filtered( Factors( AbsInt( NumeratorRat( x ) ) ),
                              p -> p in pi ) );
  end );

#############################################################################
##
#M  GcdOp( <R>, <x>, <y> ) . . . . . . . .  for Z_pi and two elements thereof
##
InstallMethod( GcdOp,
               "for Z_pi and two elements thereof", ReturnTrue,
               [ IsZ_pi, IsRat, IsRat ], 0,

  function ( R, x, y )
    if not x in R or not y in R then return fail; fi;
    return Gcd( StandardAssociate( R, x ), StandardAssociate( R, y ) );
  end );

#############################################################################
##
#M  LcmOp( <R>, <x>, <y> ) . . . . . . . .  for Z_pi and two elements thereof
##
InstallMethod( LcmOp,
               "for Z_pi and two elements thereof", ReturnTrue,
               [ IsZ_pi, IsRat, IsRat ], 0,

  function ( R, x, y )
    if not x in R or not y in R then return fail; fi;
    return Lcm( StandardAssociate( R, x ), StandardAssociate( R, y ) );
  end );

#############################################################################
##
#M  Factors( <R>, <x> ) . . . . . . . . . . . .  for Z_pi and element thereof
##
InstallMethod( Factors,
               "for Z_pi and element thereof", ReturnTrue,
               [ IsZ_pi, IsRat ], 0,

  function ( R, x )

    local  pi, p;

    if not x in R then return fail; fi;
    pi := NoninvertiblePrimes( R );
    p := Filtered( Factors( AbsInt( NumeratorRat( x ) ) ), q -> q in pi );
    if   x = Product( p ) then return p;
    else return Concatenation( [ x / Product(p) ], p ); fi;
  end );

#############################################################################
##
#M  IsUnit( <R>, <x> ) . . . . . . . . . . . . . for Z_pi and element thereof
##
InstallMethod( IsUnit,
               "for Z_pi and element thereof", ReturnTrue,
               [ IsZ_pi, IsRat ], 0,

  function ( R, x )

    local  pi;

    if not x in R then return fail; fi; if x = 0 then return false; fi;
    pi := NoninvertiblePrimes( R );
    return Intersection( Factors( AbsInt( NumeratorRat( x ) ) ), pi ) = [ ];
  end );

#############################################################################
##
#M  IsIrreducibleRingElement( <R>, <x> ) . . . . for Z_pi and element thereof
##
InstallMethod( IsIrreducibleRingElement,
               "for Z_pi and element thereof", ReturnTrue,
               [ IsZ_pi, IsRat ], 0,

  function ( R, x )

    local  pi;

    if not x in R then return fail; fi;
    pi := NoninvertiblePrimes( R );
    return Length( Filtered( Factors( AbsInt( NumeratorRat( x ) ) ),
                             q -> q in pi ) ) = 1;
  end );

#############################################################################
##
#E  z_pi.gi . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
