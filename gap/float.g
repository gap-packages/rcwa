#############################################################################
##
#W  float.g                  GAP4 Package `RCWA'                  Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains basic methods for floats.
##
Revision.float_g :=
  "@(#)$Id$";

#############################################################################
##
#C  IsFloat . . . . . . . . . . . . . . . . . . . . . . . . . . . . . C float
##
DeclareSynonym( "IsFloat", IS_FLOAT );

#############################################################################
##
#M  AbsoluteValue( x ) . . . . . . . . . . . . . . . . . . . . . . for floats
##
InstallOtherMethod( AbsoluteValue,
                    "for floats", true, [ IsFloat ], 0,

  function ( x )
    if x < FLOAT_INT(0) then return -x; else return x; fi;
  end );

#############################################################################
##
#O  Float( x ) . . . . . . . . . . . . . . . . . floating point approximation
##
DeclareOperation( "Float", [ IsObject ] );

#############################################################################
##
#M  Float( n ) . . . . . . . . . . . . . . . . . . . . . . . . . for integers
##
InstallMethod( Float,
               "for integers", true, [ IsInt ], 0, n -> FLOAT_INT(n) );

#############################################################################
##
#M  Float( x ) . . . . . . . . . . . . . . . . . . . . . . . .  for rationals
##
InstallMethod( Float,
               "for rationals", true, [ IsRat ], 0,
               x -> FLOAT_INT(  NumeratorRat(x))/
                    FLOAT_INT(DenominatorRat(x)) );

#############################################################################
##
#M  Int( x ) . . . . . . . . . . . . . . . . . . . . . . . . . . . for floats
##
InstallMethod( Int,
               "for floats", true, [ IsFloat ], 0,

  function ( x )

    local  n, pow2, sign;

    x := FLOOR_FLOAT(x);
    if x < 0 then x := -x; sign := -1; else sign := 1; fi;
    if x > 2^28-1   then return fail; fi;
    if x < Float(1) then return 0;    fi;
    pow2 := 2^26; n := 2^27;
    while Float(n) <> x do
      if Float(n) < x then n := n + pow2; else n := n - pow2; fi;
      pow2 := pow2 / 2;
    od;
    return n * sign;
  end );

#############################################################################
##
#M  Rat( x ) . . . . . . . . . . . . . . . . . . . . . . . . . . . for floats
##
InstallOtherMethod( Rat,
                    "for floats", true, [ IsFloat ], 0,

  function ( x )

    local  M, a_i, i, sign;

    i := 0; M := [[1,0],[0,1]];
    if x < 0 then sign := -1; x := -x; else sign := 1; fi;
    repeat
      a_i := Int(x); i := i + 1;
      M := M * [[a_i,1],[1,0]];
      if x - a_i > 1/10000 then x := 1/(x - a_i); else break; fi;
    until M[1][1] * FLOOR_FLOAT(x) > 10000;
    return sign * M[1][1]/M[2][1];
  end );

#############################################################################
##
#M  \<( x ) . . . . . . . . . . . . . . . . . . . . .  for rational and float
##
InstallMethod( \<,
               "for rational and float", ReturnTrue, [ IsRat, IsFloat ], 0,
               function ( x, y ) return Float(x) < y; end );

#############################################################################
##
#M  \<( x ) . . . . . . . . . . . . . . . . . . . . .  for float and rational
##
InstallMethod( \<,
               "for float and rational", ReturnTrue, [ IsFloat, IsRat ], 0,
               function ( x, y ) return x < Float(y); end );

#############################################################################
##
#M  \+( x ) . . . . . . . . . . . . . . . . . . . . .  for float and rational
##
InstallOtherMethod( \+,
                    "for float and rational", ReturnTrue, [ IsFloat, IsRat ],
                    0, function ( x, y ) return x + Float(y); end );

#############################################################################
##
#M  \+( x ) . . . . . . . . . . . . . . . . . . . . .  for rational and float
##
InstallOtherMethod( \+,
                    "for rational and float", ReturnTrue, [ IsRat, IsFloat ],
                    0, function ( x, y ) return Float(x) + y; end );

#############################################################################
##
#M  \*( x ) . . . . . . . . . . . . . . . . . . . . .  for float and rational
##
InstallOtherMethod( \*,
                    "for float and rational", ReturnTrue, [ IsFloat, IsRat ],
                    0, function ( x, y ) return x * Float(y); end );

#############################################################################
##
#M  \*( x ) . . . . . . . . . . . . . . . . . . . . .  for rational and float
##
InstallOtherMethod( \*,
                    "for rational and float", ReturnTrue, [ IsRat, IsFloat ],
                    0, function ( x, y ) return Float(x) * y; end );

#############################################################################
##
#E  float.g . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
