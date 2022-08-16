#############################################################################
##
#W  rcwamap.gi                GAP4 Package `RCWA'                 Stefan Kohl
##
##  This file contains implementations of methods and functions for computing
##  with rcwa mappings of
##
##    - the ring Z of the integers, of
##    - the ring Z^2, of
##    - the semilocalizations Z_(pi) of the ring of integers, and of
##    - the polynomial rings GF(q)[x] in one variable over a finite field.
##
##  See the definitions given in the file rcwamap.gd.
##
#############################################################################

#############################################################################
##
#F  RCWAInfo . . . . . . . . . . . . . . . . . . set info level of `InfoRCWA'
##
InstallGlobalFunction( RCWAInfo,
                       function ( n ) SetInfoLevel( InfoRCWA, n ); end );

#############################################################################
##
#S  Shorthands for commonly used filters. ///////////////////////////////////
##
#############################################################################

BindGlobal( "IsRcwaMappingInStandardRep",
             IsRcwaMapping and IsRcwaMappingStandardRep );
BindGlobal( "IsRcwaMappingOfZInStandardRep",
             IsRcwaMappingOfZ and IsRcwaMappingStandardRep );
BindGlobal( "IsRcwaMappingOfZ_piInStandardRep",
             IsRcwaMappingOfZ_pi and IsRcwaMappingStandardRep );
BindGlobal( "IsRcwaMappingOfZOrZ_piInStandardRep",
             IsRcwaMappingOfZOrZ_pi and IsRcwaMappingStandardRep );
BindGlobal( "IsRcwaMappingOfZxZInStandardRep",
             IsRcwaMappingOfZxZ and IsRcwaMappingStandardRep );
BindGlobal( "IsRcwaMappingOfGFqxInStandardRep",
             IsRcwaMappingOfGFqx and IsRcwaMappingStandardRep );

BindGlobal( "IsRcwaMappingInSparseRep",
             IsRcwaMapping and IsRcwaMappingSparseRep );
BindGlobal( "IsRcwaMappingOfZInSparseRep",
             IsRcwaMappingOfZ and IsRcwaMappingSparseRep );
BindGlobal( "IsRcwaMappingOfZ_piInSparseRep",                 # unused so far
             IsRcwaMappingOfZ_pi and IsRcwaMappingSparseRep );
BindGlobal( "IsRcwaMappingOfZOrZ_piInSparseRep",
             IsRcwaMappingOfZOrZ_pi and IsRcwaMappingSparseRep );
BindGlobal( "IsRcwaMappingOfZxZInSparseRep",                  # unused so far
             IsRcwaMappingOfZxZ and IsRcwaMappingSparseRep );
BindGlobal( "IsRcwaMappingOfGFqxInSparseRep",                 # unused so far
             IsRcwaMappingOfGFqx and IsRcwaMappingSparseRep );

#############################################################################
##
#S  The families of rcwa mappings. //////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#V  RcwaMappingsOfZFamily . . . . . . .  the family of all rcwa mappings of Z
##
BindGlobal( "RcwaMappingsOfZFamily",
            NewFamily( "RcwaMappingsFamily( Integers )",
                       IsRcwaMappingOfZ,
                       CanEasilySortElements, CanEasilySortElements ) );
SetFamilySource( RcwaMappingsOfZFamily, FamilyObj( 1 ) );
SetFamilyRange ( RcwaMappingsOfZFamily, FamilyObj( 1 ) );
SetUnderlyingRing( RcwaMappingsOfZFamily, Integers );

#############################################################################
##
#V  RcwaMappingsOfZxZFamily . . . . .  the family of all rcwa mappings of Z^2
##
BindGlobal( "RcwaMappingsOfZxZFamily",
            NewFamily( "RcwaMappingsFamily( Integers^2 )",
                       IsRcwaMappingOfZxZ,
                       CanEasilySortElements, CanEasilySortElements ) );
SetFamilySource( RcwaMappingsOfZxZFamily, FamilyObj( [ 1, 1 ] ) );
SetFamilyRange ( RcwaMappingsOfZxZFamily, FamilyObj( [ 1, 1 ] ) );
SetUnderlyingLeftModule( RcwaMappingsOfZxZFamily, Integers^2 );

## Internal variables storing the rcwa mapping families used in the
## current GAP session.

BindGlobal( "Z_PI_RCWAMAPPING_FAMILIES", [] );
BindGlobal( "GFQX_RCWAMAPPING_FAMILIES", [] );

#############################################################################
##
#F  RcwaMappingsOfZ_piFamily( <R> )
##
##  Returns the family of all rcwa mappings of a given semilocalization <R>
##  of the ring of integers.
##
InstallGlobalFunction( RcwaMappingsOfZ_piFamily,

  function ( R )

    local  fam, name;

    if   not IsZ_pi( R )
    then Error("usage: RcwaMappingsOfZ_piFamily( <R> )\n",
               "where <R> = Z_pi( <pi> ) for a set of primes <pi>.\n");
    fi;
    fam := First( Z_PI_RCWAMAPPING_FAMILIES,
                  fam -> UnderlyingRing( fam ) = R );
    if fam <> fail then return fam; fi;
    name := Concatenation( "RcwaMappingsFamily( ",
                           String( R ), " )" );
    fam := NewFamily( name, IsRcwaMappingOfZ_pi,
                      CanEasilySortElements, CanEasilySortElements );
    SetUnderlyingRing( fam, R );
    SetFamilySource( fam, FamilyObj( 1 ) );
    SetFamilyRange ( fam, FamilyObj( 1 ) );
    MakeReadWriteGlobal( "Z_PI_RCWAMAPPING_FAMILIES" );
    Add( Z_PI_RCWAMAPPING_FAMILIES, fam );
    MakeReadOnlyGlobal( "Z_PI_RCWAMAPPING_FAMILIES" );

    return fam;
  end );

#############################################################################
##
#F  RcwaMappingsOfGFqxFamily( <R> )
##
##  Returns the family of all rcwa mappings of a given polynomial ring <R>
##  in one variable over a finite field.
##
InstallGlobalFunction( RcwaMappingsOfGFqxFamily,

  function ( R )

    local  fam, x;

    if   not (     IsUnivariatePolynomialRing( R )
               and IsFiniteFieldPolynomialRing( R ) )
    then Error("usage: RcwaMappingsOfGFqxFamily( <R> ) for a ",
               "univariate polynomial ring <R> over a finite field.\n");
    fi;
    x := IndeterminatesOfPolynomialRing( R )[ 1 ];
    fam := First( GFQX_RCWAMAPPING_FAMILIES,
                  fam -> IsIdenticalObj( UnderlyingRing( fam ), R ) );
    if fam <> fail then return fam; fi;
    fam := NewFamily( Concatenation( "RcwaMappingsFamily( ",
                                      String( R ), " )" ),
                      IsRcwaMappingOfGFqx,
                      CanEasilySortElements, CanEasilySortElements );
    SetUnderlyingIndeterminate( fam, x );
    SetUnderlyingRing( fam, R );
    SetFamilySource( fam, FamilyObj( x ) );
    SetFamilyRange ( fam, FamilyObj( x ) );
    MakeReadWriteGlobal( "GFQX_RCWAMAPPING_FAMILIES" );
    Add( GFQX_RCWAMAPPING_FAMILIES, fam );
    MakeReadOnlyGlobal( "GFQX_RCWAMAPPING_FAMILIES" );

    return fam;
  end );

#############################################################################
##
#F  RcwaMappingsFamily( <R> ) . . . family of rcwa mappings over the ring <R>
##
InstallGlobalFunction( RcwaMappingsFamily,

  function ( R )

    if   IsIntegers( R ) then return RcwaMappingsOfZFamily;
    elif IsZxZ( R )      then return RcwaMappingsOfZxZFamily;
    elif IsZ_pi( R )     then return RcwaMappingsOfZ_piFamily( R );
    elif IsUnivariatePolynomialRing( R ) and IsFiniteFieldPolynomialRing( R )
    then return RcwaMappingsOfGFqxFamily( R );
    else Error("Sorry, rcwa mappings over ",R," are not yet implemented.\n");
    fi;
  end );

#############################################################################
##
#F  RcwaMappingsType( <R> ) . . . . . . . . . .  filter: rcwa mappings of <R>
##
InstallGlobalFunction( RcwaMappingsType,

  function ( R )
    if   IsIntegers( R ) then return IsRcwaMappingOfZ;
    elif IsZxZ( R )      then return IsRcwaMappingOfZxZ;
    elif IsZ_pi( R )     then return IsRcwaMappingOfZ_pi;
    elif IsUnivariatePolynomialRing( R ) and IsFiniteFieldPolynomialRing( R )
    then return IsRcwaMappingOfGFqx;
    else return fail; fi;
  end );

#############################################################################
##
#S  The methods for the general-purpose constructor for rcwa mappings. //////
##
#############################################################################

#############################################################################
##
#F  RCWAMAPPING_COMPRESS_COEFFICIENT_LIST( <coeffs> ) . . . . . . . . utility
##
##  This function takes care of that equal coefficient triples are always
##  also identical, in order to save memory.
##
BindGlobal( "RCWAMAPPING_COMPRESS_COEFFICIENT_LIST",

  function ( coeffs )

    local  cset, i;

    cset := Set(coeffs);
    for i in [1..Length(coeffs)] do
      coeffs[i] := cset[PositionSorted(cset,coeffs[i])];
    od;
  end );

#############################################################################
##
#M  RcwaMapping( <R>, <modulus>, <coeffs> ) . . . .  method (a) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping by ring, modulus and coefficients (RCWA)",
               ReturnTrue, [ IsRing, IsRingElement, IsList ], 0,

  function ( R, modulus, coeffs )

    if not modulus in R then TryNextMethod(); fi;
    if   IsIntegers(R) or IsZ_pi(R)
    then return RcwaMapping(R,coeffs);
    elif IsPolynomialRing(R)
    then return RcwaMapping(Size(LeftActingDomain(R)),modulus,coeffs);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  RcwaMapping( <R>, <modulus>, <coeffs> ) . . . .  method (a) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping by ring = Z^2, modulus and coefficients (RCWA)",
               ReturnTrue, [ IsRowModule, IsMatrix, IsList ], 0,

  function ( R, modulus, coeffs )

    local  residues, errormessage, i;

    errormessage := Concatenation("construction of an rcwa mapping of Z^2:",
                                  "\nmathematically incorrect arguments.\n");

    if   not IsZxZ(R) or DimensionsMat(modulus) <> [2,2]
      or not ForAll(Flat(modulus),IsInt) or DeterminantMat(modulus) = 0
      or Length(coeffs) <> DeterminantMat(modulus)
      or not ForAll(coeffs,IsList)
      or not Set(List(coeffs,Length)) in [[2],[3]]
      or not (    Length(coeffs[1])=2
              and ForAll( coeffs, c ->    c[1] in R and IsList(c[2])
                                      and Length(c[2])=3
                                      and IsMatrix(c[2][1])
                                      and ForAll(Flat(c[2][1]),IsInt)
                                      and c[2][2] in R
                                      and IsInt(c[2][3]) and c[2][3] <> 0 )
            or    Length(coeffs[1])=3
              and ForAll( coeffs, c ->    IsMatrix(c[1])
                                      and ForAll(Flat(c[1]),IsInt)
                                      and c[2] in R
                                      and IsInt(c[3]) and c[3] <> 0 ) )
    then Error(errormessage); return fail; fi;

    modulus  := HermiteNormalFormIntegerMat(modulus);
    residues := AllResidues(R,modulus);

    if Length(coeffs[1]) = 2 then
      for i in [1..Length(coeffs)] do
        coeffs[i][1] := coeffs[i][1] mod modulus;
      od;
      Sort( coeffs, function ( c1, c2 ) return c1[1] < c2[1]; end );
      if   List(coeffs,c->c[1]) <> residues
      then Error(errormessage); return fail; fi;
      coeffs := List(coeffs,c->c[2]);
    fi;

    if   not ForAll( [1..Length(residues)],
                     i ->   ( residues[i]*coeffs[i][1] + coeffs[i][2] )
                          mod coeffs[i][3] = [ 0, 0 ] )
    then Error(errormessage); return fail; fi;

    return RcwaMappingNC(R,modulus,coeffs);
  end );

#############################################################################
##
#M  RcwaMappingNC( <R>, <modulus>, <coeffs> ) . . NC-method (a) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping by ring, modulus and coefficients (RCWA)",
               ReturnTrue, [ IsRing, IsRingElement, IsList ], 0,

  function ( R, modulus, coeffs )

    if not modulus in R then TryNextMethod(); fi;
    if   IsIntegers(R) or IsZ_pi(R)
    then return RcwaMappingNC(R,coeffs);
    elif IsPolynomialRing(R)
    then return RcwaMappingNC(Size(LeftActingDomain(R)),modulus,coeffs);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  RcwaMappingNC( <R>, <modulus>, <coeffs> ) . . NC-method (a) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping by ring = Z^2, modulus and coefficients (RCWA)",
               ReturnTrue, [ IsRowModule, IsMatrix, IsList ], 0,

  function ( R, modulus, coeffs )

    local  ReduceRcwaMappingOfZxZ, result;

    ReduceRcwaMappingOfZxZ := function ( f )

      local  m, c, d, divs, res, resRed, mRed, cRed,
             nraffs, identres, pos, i;

      m := f!.modulus; c := f!.coeffs;
      for i in [1..Length(c)] do
        c[i] := c[i]/Gcd(Flat(c[i]));
        if c[i][3] < 0 then c[i] := -c[i]; fi;
      od;
      nraffs := Length(Set(c));
      res    := AllResidues(R,m);
      divs   := Superlattices(m);
      mRed := m; cRed := c;
      for d in divs do
        if DeterminantMat(d) < nraffs then continue; fi;
        resRed   := List(res,r->r mod d);
        identres := EquivalenceClasses([1..Length(c)],i->resRed[i]);
        if ForAll(identres,res->Length(Set(c{res}))=1) then
          mRed   := d;
          pos    := List(identres,cl->cl[1]);
          resRed := res{pos};
          cRed   := Permuted(c{pos},SortingPerm(resRed));
          break;
        fi;
      od;
      RCWAMAPPING_COMPRESS_COEFFICIENT_LIST(cRed);
      f!.modulus := Immutable(mRed);
      f!.coeffs  := Immutable(cRed);
    end;

    if not IsZxZ( R ) then TryNextMethod( ); fi;

    modulus := HermiteNormalFormIntegerMat( modulus );

    result := Objectify( NewType( RcwaMappingsOfZxZFamily,
                                  IsRcwaMappingOfZxZInStandardRep ),
                         rec( modulus := modulus,
                              coeffs  := coeffs ) );
    SetSource( result, R );
    SetRange ( result, R );

    ReduceRcwaMappingOfZxZ( result );

    return result;
  end );

#############################################################################
##
#M  RcwaMapping( <R>, <coeffs> ) . . . . . . . . . . method (b) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping by ring and coefficients (RCWA)",
               ReturnTrue, [ IsRing, IsList ], 0,

  function ( R, coeffs )

    if   IsIntegers(R)
    then return RcwaMapping(coeffs);
    elif IsZ_pi(R)
    then return RcwaMapping(NoninvertiblePrimes(R),coeffs);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  RcwaMappingNC( <R>, <coeffs> ) . . . . . . .  NC-method (b) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping by ring and coefficients (RCWA)",
               ReturnTrue, [ IsRing, IsList ], 0,

  function ( R, coeffs )

    if   IsIntegers(R)
    then return RcwaMappingNC(coeffs);
    elif IsZ_pi(R)
    then return RcwaMappingNC(NoninvertiblePrimes(R),coeffs);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  RcwaMapping( <coeffs> ) . . . . . . . . . . . .  method (c) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping of Z by coefficients (RCWA)",
               true, [ IsList ], 10,

  function ( coeffs )

    local  quiet;

    if not IsList( coeffs[1] ) or not IsInt( coeffs[1][1] )
      or Length( coeffs[1] ) = 5
    then TryNextMethod( ); fi;
    quiet := ValueOption("BeQuiet") = true;
    if not (     ForAll(Flat(coeffs),IsInt)
             and ForAll(coeffs, IsList)
             and ForAll(coeffs, c -> Length(c) = 3)
             and ForAll([0..Length(coeffs) - 1],
                        n -> coeffs[n + 1][3] <> 0 and
                             (n * coeffs[n + 1][1] + coeffs[n + 1][2])
                             mod coeffs[n + 1][3] = 0 and
                             (  (n + Length(coeffs)) * coeffs[n + 1][1] 
                              +  coeffs[n + 1][2])
                             mod coeffs[n + 1][3] = 0))
    then if quiet then return fail; fi;
         Error("the coefficients ",coeffs," do not define a proper ",
               "rcwa mapping of Z.\n");
    fi;
    return RcwaMappingNC( coeffs );
  end );

#############################################################################
##
#M  RcwaMappingNC( <coeffs> ) . . . . . . . . . . NC-method (c) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping of Z by coefficients (RCWA)",
               true, [ IsList ], 10,

  function ( coeffs )

    local  ReduceRcwaMappingOfZ, Result;

    ReduceRcwaMappingOfZ := function ( f )

      local  c, m, fact, p, cRed, cRedBuf, n;

      c := f!.coeffs; m := f!.modulus;
      for n in [1..Length(c)] do
        c[n] := c[n]/Gcd(c[n]);
        if c[n][3] < 0 then c[n] := -c[n]; fi;
      od;
      fact := Set(FactorsInt(m)); cRed := c;
      for p in fact do
        repeat
          cRedBuf := StructuralCopy(cRed);
          cRed := List([1..p], i -> cRedBuf{[(i - 1) * m/p + 1 .. i * m/p]});
          if   Length(Set(cRed)) = 1
          then cRed := cRed[1]; m := m/p; else cRed := cRedBuf; fi;
        until cRed = cRedBuf or m mod p <> 0;
      od;
      RCWAMAPPING_COMPRESS_COEFFICIENT_LIST(cRed);
      f!.coeffs  := Immutable(cRed);
      f!.modulus := Length(cRed);
    end;

    if not IsList( coeffs[1] ) or not IsInt( coeffs[1][1] )
      or Length( coeffs[1] ) = 5
    then TryNextMethod( ); fi;
    Result := Objectify( NewType(    RcwaMappingsOfZFamily,
                                     IsRcwaMappingOfZInStandardRep ),
                         rec( coeffs  := coeffs,
                              modulus := Length(coeffs) ) );
    SetSource(Result, Integers);
    SetRange (Result, Integers);
    ReduceRcwaMappingOfZ(Result);
    return Result;
  end );

#############################################################################
##
#M  RcwaMapping( <perm>, <range> ) . . . . . . . . . method (d) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping of Z by permutation and range (RCWA)",
               true, [ IsPerm, IsRange ], 0,

  function ( perm, range )

    local  quiet;

    quiet := ValueOption("BeQuiet") = true;
    if   Permutation(perm,range) = fail
    then if quiet then return fail; fi;
         Error("the permutation ",perm," does not act on the range ",
               range,".\n");
    fi;
    return RcwaMappingNC( perm, range );
  end );

#############################################################################
##
#M  RcwaMappingNC( <perm>, <range> ) . . . . . .  NC-method (d) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping of Z by permutation and range (RCWA)",
               true, [ IsPerm, IsRange ], 0,

  function ( perm, range )

    local  result, coeffs, min, max, m, n, r;

    min := Minimum(range); max := Maximum(range);
    m := max - min + 1; coeffs := [];
    for n in [min..max] do
      r := n mod m + 1;
      coeffs[r] := [1, n^perm - n, 1];
    od;
    result := RcwaMappingNC( coeffs );
    SetIsBijective(result,true);
    SetIsTame(result,true); SetIsIntegral(result,true);
    SetOrder(result,Order(RestrictedPerm(perm,range)));
    return result;
  end );

#############################################################################
##
#M  RcwaMapping( <modulus>, <values> ) . . . . . . . method (e) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping of Z by modulus and values (RCWA)",
               true, [ IsInt, IsList ], 0,

  function ( modulus, values )

    local  f, coeffs, pts, r, quiet;

    quiet := ValueOption("BeQuiet") = true;
    coeffs := [];
    for r in [1..modulus] do
      pts := Filtered(values, pt -> pt[1] mod modulus = r - 1);
      if   Length(pts) < 2
      then if quiet then return fail; fi;
           Error("the mapping is not given at at least 2 points <n> ",
                 "with <n> mod ",modulus," = ",r - 1,".\n");
      fi;
    od;
    f := RcwaMappingNC( modulus, values );
    if Mod(f) mod Div(f) <> 0 or not ForAll(values,t -> t[1]^f = t[2])
    then if quiet then return fail; fi;
         Error("the values ",values," do not define a proper ",
               "rcwa mapping of Z.\n"); 
    fi;
    return f;
  end );

#############################################################################
##
#M  RcwaMappingNC( <modulus>, <values> ) . . . .  NC-method (e) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping of Z by modulus and values (RCWA)",
               true, [ IsInt, IsList ], 0,

  function ( modulus, values )

    local  coeffs, pts, r;

    coeffs := [];
    for r in [1..modulus] do
      pts := Filtered(values, pt -> pt[1] mod modulus = r - 1);
      coeffs[r] := [  pts[1][2] - pts[2][2],
                      pts[1][2] * (pts[1][1] - pts[2][1])
                    - pts[1][1] * (pts[1][2] - pts[2][2]),
                      pts[1][1] - pts[2][1]];
    od;
    return RcwaMappingNC( coeffs );
  end );

#############################################################################
##
#M  RcwaMapping( <pi>, <coeffs> ) . . . . . . . . .  method (f) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping by noninvertible primes and coeff's (RCWA)",
               true, [ IsObject, IsList ], 0,

  function ( pi, coeffs )

    local  R, quiet;

    quiet := ValueOption("BeQuiet") = true;
    if IsInt(pi) then pi := [pi]; fi; R := Z_pi(pi);
    if not (     IsList(pi) and ForAll(pi,IsInt)
             and IsSubset(Union(pi,[1]),Set(Factors(Length(coeffs))))
             and ForAll(Flat(coeffs), x -> IsRat(x) and Intersection(pi,
                                        Set(Factors(DenominatorRat(x))))=[])
             and ForAll(coeffs, IsList)
             and ForAll(coeffs, c -> Length(c) = 3)
             and ForAll([0..Length(coeffs) - 1],
                        n -> coeffs[n + 1][3] <> 0 and
                             NumeratorRat(n * coeffs[n + 1][1]
                                            + coeffs[n + 1][2])
                             mod StandardAssociate(R,coeffs[n + 1][3]) = 0
                         and NumeratorRat(  (n + Length(coeffs))
                                           * coeffs[n + 1][1]
                                           + coeffs[n + 1][2])
                             mod StandardAssociate(R,coeffs[n + 1][3]) = 0))
    then if quiet then return fail; fi;
         Error("the coefficients ",coeffs," do not define a proper ",
               "rcwa mapping of Z_(",pi,").\n");
    fi;
    return RcwaMappingNC(pi,coeffs);
  end );

#############################################################################
##
#M  RcwaMappingNC( <pi>, <coeffs> ) . . . . . . . NC-method (f) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping by noninvertible primes and coeff's (RCWA)",
               true, [ IsObject, IsList ], 0,

  function ( pi, coeffs )

    local  ReduceRcwaMappingOfZ_pi, f, R, fam;

    ReduceRcwaMappingOfZ_pi := function ( f )

      local  c, m, pi, d_pi, d_piprime, divs, d, cRed, n, i;

      c := f!.coeffs; m := f!.modulus;
      pi := NoninvertiblePrimes(Source(f));
      for n in [1..Length(c)] do
        if c[n][3] < 0 then c[n] := -c[n]; fi;
        d_pi := Gcd(Product(Filtered(Factors(Gcd(NumeratorRat(c[n][1]),
                                                 NumeratorRat(c[n][2]))),
                                     p -> p in pi or p = 0)),
                    NumeratorRat(c[n][3]));
        d_piprime := c[n][3]/Product(Filtered(Factors(NumeratorRat(c[n][3])),
                                              p -> p in pi));
        c[n] := c[n] / (d_pi * d_piprime);
      od;
      divs := DivisorsInt(m); i := 1;
      repeat
        d := divs[i]; i := i + 1;
        cRed := List([1..m/d], i -> c{[(i - 1) * d + 1 .. i * d]});
      until Length(Set(cRed)) = 1;
      cRed := cRed[1];
      RCWAMAPPING_COMPRESS_COEFFICIENT_LIST(cRed);
      f!.coeffs  := Immutable(cRed);
      f!.modulus := Length(cRed);
    end;

    if IsInt(pi) then pi := [pi]; fi;
    if   not IsList(pi) or not ForAll(pi,IsInt) or not ForAll(coeffs,IsList)
    then TryNextMethod(); fi;
    R := Z_pi(pi); fam := RcwaMappingsFamily( R );
    f := Objectify( NewType( fam, IsRcwaMappingOfZ_piInStandardRep ),
                    rec( coeffs  := coeffs,
                         modulus := Length(coeffs) ) );
    SetSource(f,R); SetRange(f,R);
    ReduceRcwaMappingOfZ_pi(f);
    return f;
  end );

#############################################################################
##
#M  RcwaMapping( <q>, <modulus>, <coeffs> ) . . . .  method (g) in the manual
##
InstallMethod( RcwaMapping,
               Concatenation("rcwa mapping by finite field size, ",
                             "modulus and coefficients (RCWA)"),
               true, [ IsInt, IsPolynomial, IsList ], 0,

  function ( q, modulus, coeffs )

    local  d, x, P, p, quiet;

    quiet := ValueOption("BeQuiet") = true;
    if not (    IsPosInt(q) and IsPrimePowerInt(q) 
            and ForAll(coeffs, IsList)
            and ForAll(coeffs, c -> Length(c) = 3) 
            and ForAll(Flat(coeffs), IsPolynomial)
            and Length(Set(List(Flat(coeffs),
                                IndeterminateNumberOfLaurentPolynomial)))=1)
    then if quiet then return fail; fi;
         Error("see RCWA manual for information on how to construct\n",
               "an rcwa mapping of a polynomial ring.\n");
    fi;
    d := DegreeOfLaurentPolynomial(modulus);
    x := IndeterminateOfLaurentPolynomial(coeffs[1][1]);
    P := AllGFqPolynomialsModDegree(q,d,x);
    if not ForAll([1..Length(P)],
                  i -> IsZero(   (coeffs[i][1]*P[i] + coeffs[i][2])
                              mod coeffs[i][3]))
    then Error("the coefficients ",coeffs," do not define a proper ",
               "rcwa mapping.\n");
    fi;
    return RcwaMappingNC( q, modulus, coeffs );
  end );

#############################################################################
##
#M  RcwaMappingNC( <q>, <modulus>, <coeffs> ) . . NC-method (g) in the manual
##
InstallMethod( RcwaMappingNC,
               Concatenation("rcwa mapping by finite field size, ",
                             "modulus and coefficients (RCWA)"),
               true, [ IsInt, IsPolynomial, IsList ], 0,

  function ( q, modulus, coeffs )

    local  ReduceRcwaMappingOfGFqx, f, R, fam, ind;

    ReduceRcwaMappingOfGFqx := function ( f )

      local  c, m, F, q, x, deg, r, fact, d, degd,
             sigma, csorted, numresred, numresd, mred, rred,
             n, l, i;

      c := f!.coeffs; m := f!.modulus;
      for n in [1..Length(c)] do
        d := Gcd(c[n]);
        c[n] := c[n]/(d * LeadingCoefficient(c[n][3]));
      od;
      deg := DegreeOfLaurentPolynomial(m);
      F := CoefficientsRing(UnderlyingRing(FamilyObj(f)));
      q := Size(F);
      x := UnderlyingIndeterminate(FamilyObj(f));
      r := AllGFqPolynomialsModDegree(q,deg,x);
      fact := Difference(Factors(m),[One(m)]);
      for d in fact do 
        degd := DegreeOfLaurentPolynomial(d);
        repeat
          numresd := q^degd; numresred := q^(deg-degd);
          mred  := m/d;
          rred  := List(r, P -> P mod mred);
          sigma := SortingPerm(rred);
          csorted := Permuted(c,sigma);
          if ForAll([1..numresred],
                    i->Length(Set(csorted{[(i-1)*numresd+1..i*numresd]}))=1)
          then m   := mred;
               deg := deg - degd;
               r := AllGFqPolynomialsModDegree(q,deg,x);
               c := csorted{[1, 1 + numresd .. 1 + (numresred-1) * numresd]};
          fi;
        until m <> mred or not IsZero(m mod d);
      od;
      RCWAMAPPING_COMPRESS_COEFFICIENT_LIST(c);
      f!.coeffs  := Immutable(c);
      f!.modulus := m;
    end;

    ind := IndeterminateNumberOfLaurentPolynomial( coeffs[1][1] );
    R   := PolynomialRing( GF( q ), [ ind ] );
    fam := RcwaMappingsFamily( R );
    f   := Objectify( NewType( fam, IsRcwaMappingOfGFqxInStandardRep ),
                      rec( coeffs  := coeffs,
                           modulus := modulus ) );
    SetUnderlyingField( f, CoefficientsRing( R ) );
    SetSource( f, R ); SetRange( f, R );
    ReduceRcwaMappingOfGFqx( f );
    return f;
  end );

#############################################################################
##
#M  RcwaMapping( <P1>, <P2> ) . . . . . . . . . . .  method (h) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping by two class partitions (RCWA)",
               true, [ IsList, IsList ], 0,

  function ( P1, P2 )

    local  result;

    if not (     ForAll(Concatenation(P1,P2),IsResidueClass)
             and Length(P1) = Length(P2)
             and Sum(List(P1,Density)) = 1
             and Union(P1) = UnderlyingRing(FamilyObj(P1[1])))
    then TryNextMethod(); fi;
    result := RcwaMappingNC(P1,P2);
    IsBijective(result);
    return result;
  end );

#############################################################################
##
#M  RcwaMappingNC( <P1>, <P2> ) . . . . . . . . . NC-method (h) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping by two class partitions (RCWA)",
               true, [ IsList, IsList ], 0,

  function ( P1, P2 )

    local  R, coeffs, m, res, r1, m1, r2, m2, i, j;

    if not IsResidueClassUnion(P1[1]) then TryNextMethod(); fi;
    R := UnderlyingRing(FamilyObj(P1[1]));
    m := Lcm(R,List(P1,Modulus)); res := AllResidues(R,m);
    coeffs := List(res,r->[1,0,1]*One(R));
    for i in [1..Length(P1)] do
      r1 := Residue(P1[i]); m1 := Modulus(P1[i]);
      r2 := Residue(P2[i]); m2 := Modulus(P2[i]);
      for j in Filtered([1..Length(res)],j->res[j] mod m1 = r1) do
        coeffs[j] := [m2,m1*r2-m2*r1,m1];
      od;
    od;
    return RcwaMappingNC(R,m,coeffs);
  end );

#############################################################################
##
#M  RcwaMappingNC( <P1>, <P2> ) . . . .  NC-method (h) in the manual, for Z^2
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping by two class partitions of Z^2 (RCWA)",
               true, [ IsList, IsList ], 0,

  function ( P1, P2 )

    local  R, coeffs, m, res, affectedpos, t, r1, m1, r2, m2, i, j;

    if not IsResidueClassUnionOfZxZ(P1[1]) then TryNextMethod(); fi;
    R := UnderlyingRing(FamilyObj(P1[1]));
    m := Lcm(List(P1,Modulus)); res := AllResidues(R,m);
    coeffs := List(res,r->[[[1,0],[0,1]],[0,0],1]);
    for i in [1..Length(P1)] do
      r1 := Residue(P1[i]); m1 := Modulus(P1[i]);
      r2 := Residue(P2[i]); m2 := Modulus(P2[i]);
      affectedpos := Filtered([1..Length(res)],j->res[j] mod m1 = r1);
      t := [m1^-1*m2,r2-r1*m1^-1*m2,1];
      t := t * Lcm(List(Flat(t),DenominatorRat));
      for i in affectedpos do coeffs[i] := t; od;
    od;
    return RcwaMappingNC(R,m,coeffs);
  end );

#############################################################################
##
#M  RcwaMapping( <cycles> ) . . . . . . . . . . . .  method (i) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping by class cycles (RCWA)", true, [ IsList ], 0,

  function ( cycles )

    local  CheckClassCycles, R;

    CheckClassCycles := function ( R, cycles )

      if not (    ForAll(cycles,IsList)
              and ForAll(Flat(cycles),S->IsResidueClass(S)
              and IsSubset(R,S)))
         or  ForAny(Combinations(Flat(cycles),2),s->Intersection(s) <> [])
      then Error("there is no rcwa mapping of ",R," having the class ",
                 "cycles ",cycles,".\n"); 
      fi;
    end;

    if   not IsList(cycles[1]) or not IsResidueClass(cycles[1][1])
    then TryNextMethod(); fi;
    R := cycles[1][1];
    if   not (IsRing(R) or IsZxZ(R))
    then R := UnderlyingRing(FamilyObj(R)); fi;
    CheckClassCycles(R,cycles);
    return RcwaMappingNC(cycles);
  end );

#############################################################################
##
#M  RcwaMapping( <cycles> ) .  method (i), variation for rc. with fixed rep's
##
InstallMethod( RcwaMapping,
               "rcwa mapping by class cycles (fixed rep's) (RCWA)",
               true, [ IsList ], 0,

  function ( cycles )

    local  CheckClassCycles, R;

    CheckClassCycles := function ( R, cycles )

      if not (    ForAll(cycles,IsList)
              and ForAll(Flat(cycles),S->IsResidueClassWithFixedRep(S)
              and UnderlyingRing(FamilyObj(S)) = R))
         or  ForAny(Combinations(Flat(cycles),2),
                    s->Intersection(List([s[1],s[2]],
                                    AsOrdinaryUnionOfResidueClasses)) <> [])
      then Error("there is no rcwa mapping of ",R," having the class ",
                 "cycles ",cycles,".\n"); 
      fi;
    end;

    if   not IsList(cycles[1])
      or not IsResidueClassWithFixedRepresentative(cycles[1][1])
    then TryNextMethod(); fi;
    R := UnderlyingRing(FamilyObj(cycles[1][1]));
    CheckClassCycles(R,cycles);
    return RcwaMappingNC(cycles);
  end );

#############################################################################
##
#M  RcwaMappingNC( <cycles> ) . . . . . . . . . . NC-method (i) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping by class cycles (RCWA)", true, [ IsList ], 0,

  function ( cycles )

    local  result, R, coeffs, m, res, cyc, pre, im, affectedpos,
           r1, r2, m1, m2, pos, i;

    if    not IsResidueClass(cycles[1][1])
      and not IsResidueClassWithFixedRepresentative(cycles[1][1])
    then TryNextMethod(); fi;

    R := cycles[1][1];
    if   not (IsRing(R) or IsZxZ(R))
    then R := UnderlyingRing(FamilyObj(R)); fi;
    if not IsIntegers(R) and not IsZ_pi(R)
      and not (     IsUnivariatePolynomialRing(R)
                and IsFiniteFieldPolynomialRing(R))
    then TryNextMethod(); fi;

    m      := Lcm(List(Union(cycles),Modulus));
    res    := AllResidues(R,m);
    coeffs := List(res,r->[1,0,1]*One(R));
    for cyc in cycles do
      if Length(cyc) <= 1 then continue; fi;
      for pos in [1..Length(cyc)] do
        pre := cyc[pos]; im := cyc[pos mod Length(cyc) + 1];
        r1 := Residue(pre); m1 := Modulus(pre);
        r2 := Residue(im);  m2 := Modulus(im);
        affectedpos := Filtered([1..Length(res)],
                                i->res[i] mod m1 = r1 mod m1);
        for i in affectedpos do coeffs[i] := [m2,m1*r2-m2*r1,m1]; od;
      od;
    od;
    if   IsIntegers(R)
    then result := RcwaMappingNC(coeffs);
    elif IsZ_pi(R)
    then result := RcwaMappingNC(R,coeffs);
    elif IsPolynomialRing(R)
    then result := RcwaMappingNC(R,Lcm(List(Flat(cycles),Modulus)),coeffs);
    fi;
    Assert(4,Order(result)=Lcm(List(cycles,Length)));
    SetIsBijective(result,true); SetIsTame(result,true);
    SetOrder(result,Lcm(List(cycles,Length)));
    return result;
  end );

#############################################################################
##
#M  RcwaMappingNC( <cycles> ) . . . . .  NC-method (i) in the manual, for Z^2
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping of Z^2 by class cycles (RCWA)", true,
               [ IsList ], 0,

  function ( cycles )

    local  result, R, coeffs, m, res, cyc, pre, im, affectedpos, t,
           r1, r2, m1, m2, pos, i;

    if   not IsResidueClass(cycles[1][1])
      or not IsResidueClassUnionOfZxZ(cycles[1][1])
    then TryNextMethod(); fi;

    R      := UnderlyingRing(FamilyObj(cycles[1][1]));
    m      := Lcm(List(Union(cycles),Modulus));
    res    := AllResidues(R,m);
    coeffs := List(res,r->[[[1,0],[0,1]],[0,0],1]);
    for cyc in cycles do
      if Length(cyc) <= 1 then continue; fi;
      for pos in [1..Length(cyc)] do
        pre := cyc[pos]; im := cyc[pos mod Length(cyc) + 1];
        r1 := Residue(pre); m1 := Modulus(pre);
        r2 := Residue(im);  m2 := Modulus(im);
        affectedpos := Filtered([1..Length(res)],i->res[i] mod m1 = r1);
        t := [m1^-1*m2,r2-r1*m1^-1*m2,1];
        t := t * Lcm(List(Flat(t),DenominatorRat));
        for i in affectedpos do coeffs[i] := t; od;
      od;
    od;
    result := RcwaMapping(R,m,coeffs);
    Assert(4,Order(result)=Lcm(List(cycles,Length)));
    SetIsBijective(result,true); SetIsTame(result,true);
    SetOrder(result,Lcm(List(cycles,Length)));
    return result;
  end );

#############################################################################
##
#M  RcwaMapping( <expression> ) . . . . . . . . . .  method (j) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping of Z by expression, given as a string (RCWA)",
               true, [ IsString ], 0,

  function ( expression )
    if   IsSubset( "0123456789-,()crs^*/", expression )
    then return RcwaMappingNC( expression );
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  RcwaMappingNC( <expression> ) . . . . . . . . NC-method (j) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping of Z by expression, given as a string (RCWA)",
               true, [ IsString ], 0,

  function ( expression )

    local  ValueExpression, ValueElementaryExpression;

    ValueElementaryExpression := function ( exp )

      local  ints, cycle, i;

      if IsSubset("0123456789-",exp) then return Int(exp); fi;
      ints := List(Filtered(SplitString(exp,"()[],crs"),
                            s->s<>""),Int);
      if   Length(ints) = 2 then
        if   's' in exp
        then return ClassShift(ints);
        else return ClassReflection(ints); fi;
      elif Length(ints) = 4 then
        return ClassTransposition(ints);
      elif Length(ints) mod 2 = 0 then
        cycle := [];
        for i in [1,3..Length(ints)-1] do
          Add(cycle,ResidueClass(ints[i],ints[i+1]));
        od;
        return RcwaMapping([cycle]);
      else Error("unknown type of rcwa permutation\n"); fi;
    end;

    ValueExpression := function ( exp )

      local  brackets, parts, part, operators,
             values, valuesexp, value, i, j;

      if   IsSubset("0123456789-,()crs",exp)
      then return ValueElementaryExpression(exp); fi;

      brackets := 0; parts := []; operators := []; part := "";
      for i in [1..Length(exp)] do
        Add(part,exp[i]);
        if   exp[i] = '(' then
          brackets := brackets + 1;
        elif exp[i] = ')' then
          brackets := brackets - 1;
          if brackets = 0 then
            Add(parts,part); part := "";
          fi;
        elif brackets = 0 and exp[i] in "*/^" then
          Add(operators,exp[i]);
          Add(parts,part{[1..Length(part)-1]}); part := "";
        fi;
      od;
      Add(parts,part);
      parts := Filtered(parts,part->Intersection(part,"0123456789")<>"");
      for i in [1..Length(parts)] do
        if   parts[i][1] = '('
        then parts[i] := parts[i]{[2..Length(parts[i])-1]}; fi;
      od;
      values    := List(parts,ValueExpression);
      valuesexp := ShallowCopy(values);
      for i in [1..Length(operators)] do
        if operators[i] = '^' then
          valuesexp[i] := valuesexp[i]^valuesexp[i+1];
          valuesexp[i+1] := fail;
        fi;
      od;
      valuesexp := Filtered(valuesexp,val->val<>fail);

      operators := Filtered(operators,op->op<>'^');
      value     := valuesexp[1];
      for i in [1..Length(operators)] do
        if   operators[i] = '*'
        then value := value * valuesexp[i+1];
        elif operators[i] = '/'
        then value := value / valuesexp[i+1];
        else Error("RcwaMapping: unknown operator: ",operators[i],"\n"); fi; 
      od;

      return value;
    end;

    return ValueExpression( BlankFreeString( expression ) );
  end );

#############################################################################
##
#M  RcwaMapping( <R>, <f>, <g> ) . rcwa mapping of Z^2 by two rcwa map's of Z
#M  RcwaMapping( <f>, <g> )
##
InstallMethod( RcwaMapping,
               "rcwa mapping of Z^2 by two rcwa mappings of Z (RCWA)",
               ReturnTrue,
               [ IsRowModule, IsRcwaMappingOfZ, IsRcwaMappingOfZ ], 0,
               function ( R, f, g )
                 if IsZxZ(R) then return RcwaMappingNC(f,g);
                             else TryNextMethod(); fi;
               end );

InstallMethod( RcwaMapping,
               "rcwa mapping of Z^2 by two rcwa mappings of Z (RCWA)",
               IsIdenticalObj, [ IsRcwaMappingOfZ, IsRcwaMappingOfZ ], 0,
               function ( f, g ) return RcwaMappingNC(f,g); end );

#############################################################################
##
#M  RcwaMappingNC( <f>, <g> ) . rcwa mapping of Z^2 by two rcwa mappings of Z
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping of Z^2 by two rcwa mappings of Z (RCWA)",
               IsIdenticalObj, [ IsRcwaMappingOfZ, IsRcwaMappingOfZ ], 0,

  function ( f, g )

    local  result, m, mf, mg, c, cf, cg, res, r, t, d, d1, d2;

    mf := Modulus(f);      mg  := Modulus(g);
    m  := [[mf,0],[0,mg]]; res := AllResidues(Integers^2,m);
    cf := Coefficients(f); cg  := Coefficients(g); c := [];
    for r in res do
      t := [cf[r[1]+1],cg[r[2]+1]];
      d := Lcm(t[1][3],t[2][3]); d1 := d/t[1][3]; d2 := d/t[2][3];
      Add(c,[[[t[1][1]*d1,0],[0,t[2][1]*d2]],[t[1][2]*d1,t[2][2]*d2],d]);
    od;
    result := RcwaMapping(Integers^2,m,c);
    if   ForAny([f,g],HasIsClassTransposition)
    then IsClassTransposition(result); fi;
    return result;
  end );

#############################################################################
##
#M  RcwaMapping( <coeffs> ) . . .  rcwa mapping of Z in sparse representation
##
InstallMethod( RcwaMapping,
               "rcwa mapping of Z in sparse representation (RCWA)",
               true, [ IsList ], 5,

  function ( coeffs )

    local  result;

    if   not ForAll(coeffs,c->IsList(c) and Length(c)=5 and ForAll(c,IsInt)) 
    then TryNextMethod(); fi;

    if ForAny(coeffs,c->c[2] = 0 or c[5] = 0) then
      Error("zero in modulus or denominator not allowed.\n");
      return fail;
    fi;
    if ForAny(Combinations([1..Length(coeffs)],2),
              i->(    coeffs[i[1]][1]-coeffs[i[2]][1])
                  mod Gcd(coeffs[i[1]][2],coeffs[i[2]][2]) = 0)
    then Error("rcwa mapping must be single-valued.\n"); return fail; fi;
    if   Sum(List(coeffs,c->1/c[2])) <> 1
    then Error("rcwa mapping must be total.\n"); return fail; fi;

    return RcwaMappingNC(coeffs);
  end );

#############################################################################
##
#M  RcwaMappingNC( <coeffs> ) . .  rcwa mapping of Z in sparse representation
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping of Z in sparse representation (RCWA)",
               true, [ IsList ], 5,

  function ( coeffs )

    local  result, modulus, coeffset, coeffcoll, cls, redcls, cl,
           d, d_red, res, res_d, div, m, r, r_red, range, i, j;

    if   not ForAll(coeffs,c->IsList(c) and Length(c)=5)
      or not ForAll(coeffs[1],IsInt)
    then TryNextMethod(); fi;

    for i in [1..Length(coeffs)] do
      coeffs[i][2] := AbsInt(coeffs[i][2]);
      coeffs[i][1] := coeffs[i][1] mod coeffs[i][2];
      coeffs[i]{[3..5]} := coeffs[i]{[3..5]}/Gcd(coeffs[i]{[3..5]});
      if coeffs[i][5] < 0 then coeffs[i]{[3..5]} := -coeffs[i]{[3..5]}; fi;
    od;

    coeffset  := Set(List(coeffs,c->c{[3..5]}));
    coeffcoll := List(coeffset,c->[]);
    for i in [1..Length(coeffs)] do
      j := PositionSorted(coeffset,coeffs[i]{[3..5]});
      Add(coeffcoll[j],coeffs[i]);
    od;

    coeffs := [];
    for i in [1..Length(coeffset)] do

      cls := Set(coeffcoll[i],c->c{[1,2]});
      if Length(cls) > 1 then

        d_red  := Gcd(DifferencesList(List(cls,cl->cl[1])));
        d_red  := Gcd(d_red,Gcd(List(cls,cl->cl[2])));
        r_red  := cls[1][1] mod d_red;
        redcls := List(cls,cl->[(cl[1]-r_red)/d_red,cl[2]/d_red]);
        m      := Lcm(List(redcls,cl->cl[2]));
        res    := [];
        for cl in redcls do
          for j in [0..m/cl[2]-1] do Add(res,cl[1]+j*cl[2]); od;
        od;
        res := Set(res);

        redcls := [];
        div    := DivisorsInt(m);
        for d in div do
          res_d := Set(res mod d);
          for r in res_d do
            range := List([0..m/d-1],j->r+j*d);
            if IsSubset(res,range) then
              Add(redcls,[r,d]);
              res := Difference(res,range);
              if res = [] then break; fi;
              if Length(res) < m/d then break; fi;
            fi;
          od;
          if res = [] then break; fi;
        od;

        cls := List(redcls,cl->[cl[1]*d_red+r_red,cl[2]*d_red]);

      # Erroneous reduction process: doesn't cope with cases like
      # 0(3) U 1(6) U 5(6) = 1(2) U 0(6).
      # 
      # repeat
      #   oldcls := ShallowCopy(cls);
      #   mods   := Set(List(oldcls,cl->cl[2]));
      #   for m in mods do
      #     resm := List(Set(Filtered(cls,cl->cl[2]=m)),c->c[1]);
      #     if Length(resm) >= 2 then
      #       for p in Set(Factors(m)) do
      #         for r in Filtered(resm,res->res<m/p) do
      #           # range := [r,r+m/p..m-m/p+r]; -> range restriction (<2^28)
      #           range := List([0..p-1],j->j*(m/p)+r);
      #           if IsSubset(resm,range) then
      #             cls := Difference(cls,List(range,r->[r,m]));
      #             Add(cls,[r,m/p]);
      #           fi;
      #         od;
      #       od;
      #     fi;
      #   od;
      #   cls := Set(cls);
      # until cls = oldcls;

      fi;

      for cl in cls do
        Add(coeffs,Concatenation(cl,coeffset[i]));
      od;

    od;

    # SortParallel(List(coeffs,c->[c[2],c[1]]),coeffs); -> problematic?
    coeffs  := Set(coeffs);
    modulus := Lcm(List(coeffs,c->c[2]));

    MakeImmutable(coeffs);
    result := Objectify( NewType( RcwaMappingsOfZFamily,
                                  IsRcwaMappingOfZ
                              and IsRcwaMappingSparseRep ),
                         rec( modulus := modulus,
                              coeffs  := coeffs ) );
    SetSource(result,Integers);
    SetRange (result,Integers);

    return result;
  end );

#############################################################################
##
#S  Conversion of rcwa mappings between standard and sparse representation. /
##
#############################################################################

#############################################################################
##
#M  SparseRepresentation( <f> )
##
InstallMethod( SparseRepresentation,
               "for rcwa mappings in standard representation (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )

    local  result, attrs, attrsetters, props, propsetters, attr, prop,
           R, coeffs, src, sparse, cl, r, m, c, i;

    R      := Source(f);
    coeffs := f!.coeffs;

    src := Set(Flat(List(LargestSourcesOfAffineMappings(f),
                         AsUnionOfFewClasses)));
    sparse := [];
    for cl in src do
      r := Residue(cl); m := Modulus(cl);
      if   IsRcwaMappingOfZ(f)
      then c := coeffs[r+1];
      else c := coeffs[Position(AllResidues(R,m),r)]; fi;
      Add(sparse,[r,m,c[1],c[2],c[3]]);
    od;

    sparse := Set(sparse);

    result := Objectify(NewType(FamilyObj(f),RcwaMappingsType(R)
                                         and IsRcwaMappingSparseRep),
                        rec(modulus := f!.modulus, coeffs := sparse));

    # Copy over representation-independent attributes and properties.

    attrs := List( Intersection( RCWA_REP_INDEPENDENT_ATTRIBUTES,
                                 KnownAttributesOfObject( f ) ),
                   ValueGlobal );
    attrsetters := List(attrs,Setter);
    for i in [1..Length(attrs)] do attrsetters[i](result,attrs[i](f)); od;

    props := List( Intersection( RCWA_REP_INDEPENDENT_PROPERTIES,
                                 KnownPropertiesOfObject( f ) ),
                   ValueGlobal );
    propsetters := List(props,Setter);
    for i in [1..Length(props)] do propsetters[i](result,props[i](f)); od;

    return result;
  end );

#############################################################################
##
#M  SparseRepresentation( <f> )
##
InstallMethod( SparseRepresentation,
               "for rcwa mappings in sparse representation (RCWA)",
               true, [ IsRcwaMappingInSparseRep ], 0, f -> f );

#############################################################################
##
#M  StandardRepresentation( <f> )
##
InstallMethod( StandardRepresentation,
               "for rcwa mappings in sparse representation (RCWA)",
               true, [ IsRcwaMappingInSparseRep ], 0,

  function ( f )

    local  result, attrs, attrsetters, props, propsetters,
           R, modulus, coeffs, src, sparse, res, cl, r, m, c, n, i;

    R       := Source(f);
    modulus := f!.modulus;
    sparse  := f!.coeffs;

    if IsRing(R) then
      coeffs := List([1..NumberOfResidues(R,modulus)],r->[1,0,1]*One(R));
    elif IsZxZ(R) then
      coeffs := List([1..NumberOfResidues(R,modulus)],
                     r->[[[1,0],[0,1]],[0,0],1]);
    fi;

    res := AllResidues(R,modulus);
    for i in [1..Length(sparse)] do
      c := sparse[i];
      r := c[1]; m := c[2];
      if IsRcwaMappingOfZ(f) then
        for n in [r+1,r+m+1..modulus-m+r+1] do
          coeffs[n] := c{[3..5]};
        od;
      else
        for n in PositionsProperty(res,el->el mod m = r) do
          coeffs[n] := c{[3..5]};
        od;
      fi;
    od;

    result := Objectify(NewType(FamilyObj(f),RcwaMappingsType(R)
                                         and IsRcwaMappingStandardRep),
                        rec( modulus := modulus, coeffs := coeffs ));

    # Copy over representation-independent attributes and properties.

    attrs := List( Intersection( RCWA_REP_INDEPENDENT_ATTRIBUTES,
                                 KnownAttributesOfObject( f ) ),
                   ValueGlobal );
    attrsetters := List(attrs,Setter);
    for i in [1..Length(attrs)] do attrsetters[i](result,attrs[i](f)); od;

    props := List( Intersection( RCWA_REP_INDEPENDENT_PROPERTIES,
                                 KnownPropertiesOfObject( f ) ),
                   ValueGlobal );
    propsetters := List(props,Setter);
    for i in [1..Length(props)] do propsetters[i](result,props[i](f)); od;

    return result;
  end );

#############################################################################
##
#M  StandardRepresentation( <f> )
##
InstallMethod( StandardRepresentation,
               "for rcwa mappings in standard representation (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0, f -> f );

#############################################################################
##
#S  ExtRepOfObj / ObjByExtRep for rcwa mappings. ////////////////////////////
##
#############################################################################

#############################################################################
##
#M  ExtRepOfObj( <f> ) . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( ExtRepOfObj,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               f -> [ Modulus( f ), ShallowCopy( Coefficients( f ) ) ] );

#############################################################################
##
#M  ExtRepOfObj( <ct> ) . . . . . . . . . . . . . .  for class transpositions
##
InstallMethod( ExtRepOfObj,
               "for class transpositions (RCWA)", true,
               [ IsRcwaMapping and IsClassTransposition ], 0,

  function ( ct )

    local  cls;

    cls := TransposedClasses(ct);
    return [ Residue(cls[1]), Mod(cls[1]), Residue(cls[2]), Mod(cls[2]) ];
  end );

#############################################################################
##
#M  ObjByExtRep( <fam>, <l> ) . rcwa mapping, by list [ <modulus>, <coeffs> ]
##
InstallMethod( ObjByExtRep,
               "rcwa mapping, by list [ <modulus>, <coefficients> ] (RCWA)",
               ReturnTrue, [ IsFamily, IsList ], 0,

  function ( fam, l )

    local  R;

    if not HasUnderlyingRing(fam) or Length(l) <> 2 then TryNextMethod(); fi;
    R := UnderlyingRing(fam);
    if fam <> RcwaMappingsFamily(R) then TryNextMethod(); fi;
    if   ForAll(l[2],c->IsList(c) and Length(c)=5)
    then return RcwaMappingNC(l[2]); # sparse rep., of Z
    else return RcwaMappingNC(R,l[1],l[2]); fi;
  end );

#############################################################################
##
#S  Creating new rcwa mappings from rcwa mappings of the same ring. /////////
##
#############################################################################

#############################################################################
##
#M  PiecewiseMapping( <sources>, <maps> ) . . . . . .  for rcwa mappings of Z
##
InstallMethod( PiecewiseMapping,
               "for rcwa mappings of Z (RCWA)",
               ReturnTrue, [ IsList, IsList ], 0,

  function ( sources, maps )

    local  map, coeffs, f, c, S, t, cls, cl, i;

    if  Length(sources) <> Length(maps)
      or not ForAll(sources,IsListOrCollection)
      or not ForAll(maps,IsMapping)
    then return fail; fi;
    if   not ForAll(sources,IsResidueClassUnionOfZ)
      or not ForAll(maps,IsRcwaMappingOfZ)
      or not IsIntegers(Union(sources))
      or Sum(List(sources,Density)) <> 1
    then TryNextMethod(); fi;

    maps := List(maps,SparseRep);
    coeffs := [];
    for i in [1..Length(maps)] do
      S := sources[i];
      f := maps[i];
      c := Coefficients(f);
      for t in c do
        cls := AsUnionOfFewClasses(Intersection(ResidueClass(t[1],t[2]),S));
        for cl in cls do
          Add(coeffs,[Residue(cl),Modulus(cl),t[3],t[4],t[5]]);
        od;
      od;
    od;
    map := RcwaMapping(coeffs);
    return SparseRep(map);
  end );

#############################################################################
##
#S  Creating new rcwa mappings from rcwa mappings of different rings. ///////
##
#############################################################################

#############################################################################
##
#F  LocalizedRcwaMapping( <f>, <p> )
##
InstallGlobalFunction( LocalizedRcwaMapping,

  function ( f, p )
    if   not IsRcwaMappingOfZ(f) or not IsInt(p) or not IsPrimeInt(p)
    then Error("usage: see ?LocalizedRcwaMapping( f, p )\n"); fi;
    return SemilocalizedRcwaMapping( f, [ p ] );
  end );

#############################################################################
##
#F  SemilocalizedRcwaMapping( <f>, <pi> )
##
InstallGlobalFunction( SemilocalizedRcwaMapping,

  function ( f, pi )
    if    IsRcwaMappingOfZ(f) and IsList(pi) and ForAll(pi,IsPosInt)
      and ForAll(pi,IsPrimeInt) and IsSubset(pi,Factors(Modulus(f)))
    then return RcwaMapping(Z_pi(pi),ShallowCopy(Coefficients(f)));
    else Error("usage: see ?SemilocalizedRcwaMapping( f, pi )\n"); fi;
  end );

#############################################################################
##
#M  ProjectionsToCoordinates( <f> ) . . . . . . . .  for rcwa mappings of Z^2
##
InstallMethod( ProjectionsToCoordinates,
               "rcwa mapping of Z^2 to two rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZxZ ], 0,

  function ( f )

    local  m, mf, mg, c, cf, cg, res, t, t1, t2, r, i;

    m := Modulus(f); c := Coefficients(f);
    res := AllResidues(Integers^2,m);
    mf := m[1][1]; mg := m[2][2]; cf := []; cg := [];
    for i in [1..Length(res)] do
      t := c[i]; r := res[i];
      t1 := [t[1][1][1],t[2][1],t[3]]; t1 := t1/Gcd(t1);
      t2 := [t[1][2][2],t[2][2],t[3]]; t2 := t2/Gcd(t2);
      if   not IsBound(cf[r[1]+1]) then cf[r[1]+1] := t1;
      elif cf[r[1]+1] <> t1        then return fail; fi;
      if   not IsBound(cg[r[2]+1]) then cg[r[2]+1] := t2;
      elif cg[r[2]+1] <> t2        then return fail; fi;
      if t[1][1][2] <> 0 or t[1][2][1] <> 0 then return fail; fi;
    od;
    return [ RcwaMapping(cf), RcwaMapping(cg) ];
  end );

#############################################################################
##
#M  Projection( <f>, <coord> ) .  proj. of an rcwa mapping of Z^2 to 1 coord.
##
InstallOtherMethod( Projection,
                    "for rcwa mappings of Z^2 (RCWA)",
                    ReturnTrue, [ IsRcwaMappingOfZxZ, IsPosInt ], 0,

  function ( f, coord )

    local  m, c, c_proj, proj;

    if not coord in [1,2] then return fail; fi; # there are only 2 coord's

    proj := ProjectionsToCoordinates(f); # maybe even both projections exist
    if proj <> fail then return proj[coord]; fi;

    m := Modulus(f); # check whether the choice of the affine partial mapping
                     # depends only on the specified coordinate:
    if   m[1][2] <> 0 or m[2][1] <> 0 or m[3-coord][3-coord] <> 1
    then return fail; fi;
 
    c := Coefficients(f); # check for dependency on other coordinate:
    if not ForAll(c,t->t[1][3-coord][coord]=0) then return fail; fi;

    # build coefficient list in one dimension:
    c_proj := List(c,t->[t[1][coord][coord],t[2][coord],t[3]]);

    return RcwaMapping(c_proj);
  end );

#############################################################################
##
#S  The automorphism switching action on negative and nonnegative integers. /
##
#############################################################################

#############################################################################
##
#M  Mirrored( <f> ) . . . . . . . . . for rcwa mappings of Z in standard rep.
#M  Mirrored( <f> ) . . . . . . . . . for rcwa mappings of Z in sparse rep.
##
InstallOtherMethod( Mirrored,
                    "for rcwa mappings of Z in standard rep. (RCWA)",
                    true, [ IsRcwaMappingOfZInStandardRep ], 0,
                    f -> f^RcwaMapping( [ [ -1, -1, 1 ] ] ) );
InstallOtherMethod( Mirrored,
                    "for rcwa mappings of Z in sparse rep. (RCWA)",
                    true, [ IsRcwaMappingOfZInSparseRep ], 0,
                    f -> f^RcwaMapping( [ [ 0, 1, -1, -1, 1 ] ] ) );

#############################################################################
##
#S  Constructors and basic methods for special types of rcwa permutations. //
##
#############################################################################

#############################################################################
##
#F  ClassShift( <R>, <r>, <m> ) . . . . . . . . . . . . . class shift nu_r(m)
#F  ClassShift( <r>, <m> )  . . . . . . . . . . . . . . . . . . . . .  (dito)
#F  ClassShift( <R>, <cl> ) . . . . . .  class shift nu_r(m), where cl = r(m)
#F  ClassShift( <cl> )  . . . . . . . . . . . . . . . . . . . . . . .  (dito)
#F  ClassShift( <R> ) . . . . . . . . . . . . .  class shift nu_R: n -> n + 1
##
##  (Enclosing the argument list in list brackets is permitted.)
##
InstallGlobalFunction( ClassShift,

  function ( arg )

    local  result, R, coeff, idcoeff, res, pos, r, m, latex;

    if Length(arg) = 1 and IsList(arg[1]) then arg := arg[1]; fi;

    if   IsZxZ(arg[1])
      or IsRowVector(arg[1]) and Length(arg[1]) = 2 and ForAll(arg[1],IsInt)
      or IsResidueClassOfZxZ(arg[1])
    then return CallFuncList(ClassShiftOfZxZ,arg); fi;

    if not Length(arg) in [1..3]
      or     Length(arg) = 1 and not IsResidueClass(arg[1])
      or     Length(arg) = 2
         and not (   ForAll(arg,IsRingElement)
                  or     IsRing(arg[1])
                     and IsResidueClass(arg[2])
                     and arg[1] = UnderlyingRing(FamilyObj(arg[2])))
      or     Length(arg) = 3
         and not (    IsRing(arg[1])
                  and IsSubset(arg[1],arg{[2,3]}))
    then Error("usage: see ?ClassShift( r, m )\n"); fi;

    if IsRing(arg[1]) then R := arg[1]; arg := arg{[2..Length(arg)]}; fi;
    if   IsBound(R) and IsEmpty(arg)
    then arg := [0,1] * One(R);
    elif IsResidueClass(arg[1])
    then if not IsBound(R) then R := UnderlyingRing(FamilyObj(arg[1])); fi;
         arg := [Residue(arg[1]),Modulus(arg[1])] * One(R);
    elif not IsBound(R) then R := DefaultRing(arg[2]); fi;
    arg := arg * One(R); # Now we know R, and we have arg = [r,m].

    m          := StandardAssociate(R,arg[2]);
    r          := arg[1] mod m;
    res        := AllResidues(R,m);
    idcoeff    := [1,0,1]*One(R);
    coeff      := List(res,r->idcoeff);
    pos        := PositionSorted(res,r);
    coeff[pos] := [1,m,1]*One(R);
    result     := RcwaMapping(R,m,coeff);
    SetIsClassShift(result,true); SetIsBijective(result,true);
    if   Characteristic(R) = 0
    then SetOrder(result,infinity);
    else SetOrder(result,Characteristic(R)); fi;
    SetIsTame(result,true);
    SetBaseRoot(result,result); SetPowerOverBaseRoot(result,1);
    if IsIntegers(R) then
      SetSmallestRoot(result,result); SetPowerOverSmallestRoot(result,1);
    fi;
    SetFactorizationIntoCSCRCT(result,[result]);

    latex := ValueOption("LaTeXString");
    if latex = fail then
      if IsOne(m) then
        SetLaTeXString(result,"\\nu");
      else
        SetLaTeXString(result,Concatenation("\\nu_{",String(r),"(",
                                                     String(m),")}"));
      fi;
    elif not IsEmpty(latex) then SetLaTeXString(result,latex); fi;

    return result;
  end );

#############################################################################
##
#F  ClassShiftOfZxZ( <R>, <r>, <m>, <coord> )  class shift nu_r(m),c; c=coord
#F  ClassShiftOfZxZ( <r>, <m>, <coord> )  . . . . . . . . . . . . . .  (dito)
#F  ClassShiftOfZxZ( <R>, <cl>, <coord> ) . .  class shift nu_r(m),c; cl=r(m)
#F  ClassShiftOfZxZ( <cl>, <coord> )  . . . . . . . . . . . . . . . .  (dito)
#F  ClassShiftOfZxZ( <R>, <coord> ) . . . . . . . . . . .  class shift nu_R_c
##
##  This function is called by `ClassShift' if the first argument is either
##  Integers^2, a row vector of length 2 with integer entries or a residue
##  class of Integers^2. Enclosing the argument list in list brackets is
##  permitted.
##
InstallGlobalFunction( ClassShiftOfZxZ,

  function ( arg )

    local  result, R, M, r, m, coord, cl, coeff, idcoeff, res, pos, latex;

    R := Integers^2; M := FullMatrixAlgebra(Integers,2);

    if Length(arg) = 1 and IsList(arg[1]) then arg := arg[1]; fi;

    coord := arg[Length(arg)]; arg := arg{[1..Length(arg)-1]};
    if IsZxZ(arg[1]) then arg := arg{[2..Length(arg)]}; fi;

    if   not coord in [1,2]
      or not Length(arg) in [0..2]
      or Length(arg) = 1 and not IsResidueClassOfZxZ(arg[1])
      or Length(arg) = 2 and not (arg[1] in R and arg[2] in M)
    then Error("usage: see ?ClassShift( r, m, coord )\n"); fi;

    if   arg = [] then cl := R;
    elif Length(arg) = 1 then cl := arg[1];
    else cl := ResidueClass(arg[1],arg[2]); fi;

    r := Residue(cl); m := Modulus(cl);

    res        := AllResidues(R,m);
    idcoeff    := [[[1,0],[0,1]],[0,0],1];
    coeff      := ListWithIdenticalEntries(Length(res),idcoeff);
    pos        := PositionSorted(res,r);
    coeff[pos] := [[[1,0],[0,1]],m[coord],1];
    result     := RcwaMapping(R,m,coeff);
    SetIsClassShift(result,true); SetIsBijective(result,true);
    SetOrder(result,infinity);
    SetIsTame(result,true);
    SetBaseRoot(result,result); SetPowerOverBaseRoot(result,1);
    SetFactorizationIntoCSCRCT(result,[result]);

    latex := ValueOption("LaTeXString");
    if latex = fail then
      latex := Concatenation("\\nu_{",ViewString(cl),",",String(coord),"}");
      latex := ReplacedString(latex,"Z","\\mathbb{Z}");
      SetLaTeXString(result,latex);
    elif not IsEmpty(latex) then SetLaTeXString(result,latex); fi;

    return result;
  end );

#############################################################################
##
#M  IsClassShift( <sigma> ) . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( IsClassShift,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               sigma -> IsResidueClass(Support(sigma))
                        and sigma = ClassShift(Support(sigma)) );

#############################################################################
##
#M  IsPowerOfClassShift( <sigma> ) . . . . . . . . . . for rcwa mappings of Z
##
InstallMethod( IsPowerOfClassShift, "for rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ ], 0,

  function ( sigma )

    local  cl, c;

    if not IsClassWiseOrderPreserving(sigma) then return false; fi;
    if IsSignPreserving(sigma) then return IsOne(sigma); fi;
    if not IsBijective(sigma) then return false; fi;
    cl := Support(sigma);
    if not IsResidueClass(cl) then return false; fi;
    if Mod(sigma) <> Mod(cl) then return false; fi;
    return true;
  end );

#############################################################################
##
#M  String( <cs> ) . . . . . . . . . . . . . . . . . . . . . for class shifts
#M  ViewString( <cs> ) . . . . . . . . . . . . . . . . . . . for class shifts
#M  PrintObj( <cs> ) . . . . . . . . . . . . . . . . . . . . for class shifts
#M  ViewObj( <cs> )  . . . . . . . . . . . . . . . . . . . . for class shifts
##
InstallMethod( String, "for class shifts (RCWA)", true,
               [ IsRcwaMapping and IsClassShift ], SUM_FLAGS,

  function ( cs )

    local  str;

    if IsRcwaMappingOfZ(cs) then
      str := Concatenation(List(["ClassShift(",Residue(Support(cs)),",",
                                 Modulus(Support(cs))],String));
    else
      str := Concatenation(List(["ClassShift(",Source(cs),",",
                                 Residue(Support(cs)),",",
                                 Modulus(Support(cs))],String));
    fi;
    if IsRcwaMappingOfZxZ(cs) then
      Append(str,",");
      Append(str,String(PositionNonZero(Residue(Support(cs))^cs
                                       -Residue(Support(cs)))));
    fi;
    return Concatenation(BlankFreeString(str),")");
  end );

InstallMethod( ViewString, "for class shifts (RCWA)", true,
               [ IsRcwaMapping and IsClassShift ], SUM_FLAGS,

  function ( cs )

    local  cl, name, suppname;

    if   ValueOption("PrintNotation") = true
    then return String(cs); fi;
    if   ValueOption("AbridgedNotation") = true
    then name := "cs"; else name := "ClassShift"; fi;
    cl := Support(cs);
    if IsRing(cl) or IsZxZ(cl) then suppname := RingToString(cl);
                               else suppname := ViewString(cl); fi;
    if   IsRing(Source(cs)) then
      return Concatenation(List([name,"( ",suppname," )"],String));
    elif IsRcwaMappingOfZxZ(cs) then
      return Concatenation(List([name,"( ",suppname,", ",
                                 PositionNonZero(Residue(Support(cs))^cs
                                                -Residue(Support(cs)))," )"],
                                String));
    else TryNextMethod(); fi;
  end );

InstallMethod( ViewString, "for powers of class shifts of Z (RCWA)", true,
               [ IsRcwaMappingOfZ and IsPowerOfClassShift ], SUM_FLAGS,

  function ( cs )
    if IsClassShift(cs) then TryNextMethod(); fi;
    return Concatenation(ViewString(ClassShift(Support(cs))),"^",
                         String(First(List(Coefficients(cs),c->c[2]),
                                      b->b<>0)/Modulus(cs)));
  end );

InstallMethod( PrintObj, "for class shifts (RCWA)", true,
               [ IsRcwaMapping and IsClassShift ], SUM_FLAGS+10,
               function ( cs ) Print( String( cs ) ); end );

InstallMethod( ViewObj, "for class shifts (RCWA)", true,
               [ IsRcwaMapping and IsClassShift ], 20,
               function ( cs ) Print( ViewString( cs ) ); end );

InstallMethod( ViewObj, "for powers of class shifts (RCWA)", true,
               [ IsRcwaMapping and IsPowerOfClassShift ], 20,
               function ( cs ) Print( ViewString( cs ) ); end );

#############################################################################
##
#F  ClassReflection( <R>, <r>, <m> )  . . . .  class reflection varsigma_r(m)
#F  ClassReflection( <r>, <m> ) . . . . . . . . . . . . . . . . . . .  (dito)
#F  ClassReflection( <R>, <cl> )  . class reflection varsigma_r(m), cl = r(m)
#F  ClassReflection( <cl> ) . . . . . . . . . . . . . . . . . . . . .  (dito)
#F  ClassReflection( <R> )  . . . . . .  class reflection varsigma_R: n -> -n
##
##  (Enclosing the argument list in list brackets is permitted.)
##
InstallGlobalFunction( ClassReflection,

  function ( arg )

    local  result, R, coeff, idcoeff, res, pos, r, m, latex;

    if Length(arg) = 1 and IsList(arg[1]) then arg := arg[1]; fi;

    if   IsZxZ(arg[1])
      or IsRowVector(arg[1]) and Length(arg[1]) = 2 and ForAll(arg[1],IsInt)
      or IsResidueClassOfZxZ(arg[1])
    then
      return CallFuncList(ClassRotationOfZxZ,
                          Concatenation(arg,[[[-1,0],[0,-1]]]));
    fi;

    if not Length(arg) in [1..3]
      or     Length(arg) = 1 and not IsResidueClass(arg[1])
      or     Length(arg) = 2
         and not (   ForAll(arg,IsRingElement)
                  or     IsRing(arg[1])
                     and IsResidueClass(arg[2])
                     and arg[1] = UnderlyingRing(FamilyObj(arg[2])))
      or     Length(arg) = 3
         and not (    IsRing(arg[1])
                  and IsSubset(arg[1],arg{[2,3]}))
    then Error("usage: see ?ClassReflection( r, m )\n"); fi;

    if IsRing(arg[1]) then R := arg[1]; arg := arg{[2..Length(arg)]}; fi;
    if   IsBound(R) and IsEmpty(arg)
    then arg := [0,1] * One(R);
    elif IsResidueClass(arg[1])
    then if not IsBound(R) then R := UnderlyingRing(FamilyObj(arg[1])); fi;
         arg := [Residue(arg[1]),Modulus(arg[1])] * One(R);
    elif not IsBound(R) then R := DefaultRing(arg[2]); fi;
    if Characteristic(R) = 2 then return One(RCWA(R)); fi; # Now we know R...
    arg := arg * One(R); # ...and we have arg = [r,m].

    m          := StandardAssociate(R,arg[2]);
    r          := arg[1] mod m;
    res        := AllResidues(R,m);
    idcoeff    := [1,0,1]*One(R);
    coeff      := List(res,r->idcoeff);
    pos        := PositionSorted(res,r);
    coeff[pos] := [-1,2*r,1]*One(R);
    result     := RcwaMapping(R,m,coeff);
    SetIsClassReflection(result,true);
    SetRotationFactor(result,-1);
    SetIsBijective(result,true);
    SetOrder(result,2); SetIsTame(result,true);
    SetFactorizationIntoCSCRCT(result,[result]);

    latex := ValueOption("LaTeXString");
    if latex = fail then
      if IsOne(m) then
        SetLaTeXString(result,"\\varsigma");
      else
        SetLaTeXString(result,Concatenation("\\varsigma_{",String(r),"(",
                                                           String(m),")}"));
      fi;
    elif not IsEmpty(latex) then SetLaTeXString(result,latex); fi;

    return result;
  end );

#############################################################################
##
#M  IsClassReflection( <sigma> ) . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( IsClassReflection,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               sigma -> IsResidueClass(Union(Support(sigma),
                                       ExcludedElements(Support(sigma)))) and
               sigma = ClassReflection(Union(Support(sigma),
                                       ExcludedElements(Support(sigma)))) );

#############################################################################
##
#M  String( <cr> ) . . . . . . . . . . . . . . . . . .  for class reflections
#M  ViewString( <cr> ) . . . . . . . . . . . . . . . .  for class reflections
##
InstallMethod( String, "for class reflections (RCWA)", true,
               [ IsRcwaMapping and IsClassReflection ], SUM_FLAGS,

  function ( cr )
    if IsRcwaMappingOfZ(cr) then
      return Concatenation(List(["ClassReflection(",
                                 Residue(Support(cr)),",",
                                 Modulus(Support(cr)),")"],BlankFreeString));
    else
      return Concatenation(List(["ClassReflection(",Source(cr),",",
                                 Residue(Support(cr)),",",
                                 Modulus(Support(cr)),")"],BlankFreeString));
    fi;
  end );

InstallMethod( ViewString, "for class reflections (RCWA)", true,
               [ IsRcwaMapping and IsClassReflection ], SUM_FLAGS,

  function ( cr )

    local  cl, name, suppname;

    if   ValueOption("PrintNotation") = true
    then return String(cr); fi;
    if   ValueOption("AbridgedNotation") = true
    then name := "cr"; else name := "ClassReflection"; fi;
    cl := Union(Support(cr),ExcludedElements(Support(cr)));
    if IsRing(cl) or IsZxZ(cl) then suppname := RingToString(cl);
                               else suppname := ViewString(cl); fi;
    return Concatenation(List([name,"( ",suppname," )"],String));
  end );

#############################################################################
##
#F  ClassRotation( <R>, <r>, <m>, <u> ) . . . . . class rotation rho_(r(m),u)
#F  ClassRotation( <r>, <m>, <u> )  . . . . . . . . . . . . . . . . .  (dito)
#F  ClassRotation( <R>, <cl>, <u> ) .  class rotation rho_(r(m),u), cl = r(m)
#F  ClassRotation( <cl>, <u> )  . . . . . . . . . . . . . . . . . . .  (dito)
#F  ClassRotation( <R>, <u> ) . . . . . . . class rotation rho_(R,u): n -> un
##
##  (Enclosing the argument list in list brackets is permitted.)
##
InstallGlobalFunction( ClassRotation,

  function ( arg )

    local  result, R, coeff, idcoeff, res, pos, r, m, u, latex;

    if Length(arg) = 1 and IsList(arg[1]) then arg := arg[1]; fi;

    if   IsZxZ(arg[1])
      or IsRowVector(arg[1]) and Length(arg[1]) = 2 and ForAll(arg[1],IsInt)
      or IsResidueClassOfZxZ(arg[1])
    then return CallFuncList(ClassRotationOfZxZ,arg); fi;

    if not Length(arg) in [2..4]
      or     Length(arg) = 2
         and not (    IsResidueClass(arg[1])
                  and IsCollsElms(FamilyObj(arg[1]),FamilyObj(arg[2])))
      or     Length(arg) = 3
         and not (   ForAll(arg,IsRingElement)
                  or     IsRing(arg[1])
                     and IsResidueClass(arg[2])
                     and arg[1] = UnderlyingRing(FamilyObj(arg[2]))
                     and arg[3] in arg[1])
      or     Length(arg) = 4
         and not (    IsRing(arg[1])
                  and IsSubset(arg[1],arg{[2,3,4]}))
    then Error("usage: see ?ClassRotation( r, m, u )\n"); fi;

    if IsRing(arg[1]) then R := arg[1]; arg := arg{[2..Length(arg)]}; fi;
    if   IsBound(R) and Length(arg) = 1
    then arg := [0,1,arg[1]] * One(R);
    elif IsResidueClass(arg[1])
    then if not IsBound(R) then R := UnderlyingRing(FamilyObj(arg[1])); fi;
         arg := [Residue(arg[1]),Modulus(arg[1]),arg[2]] * One(R);
    elif not IsBound(R) then R := DefaultRing(arg{[2,3]}); fi;
    arg := arg * One(R); # Now we know R, and we have arg = [r,m,u].

    m          := StandardAssociate(R,arg[2]);
    r          := arg[1] mod m;
    u          := arg[3];

    if   IsOne( u) then return One(RCWA(R));
    elif IsOne(-u) then return ClassReflection(ResidueClass(R,m,r)); fi;

    res        := AllResidues(R,m);
    idcoeff    := [1,0,1]*One(R);
    coeff      := List(res,r->idcoeff);
    pos        := PositionSorted(res,r);
    coeff[pos] := [u,(1-u)*r,1]*One(R);
    result     := RcwaMapping(R,m,coeff);
    SetIsClassRotation(result,true);
    SetRotationFactor(result,u);
    SetIsBijective(result,true);
    SetOrder(result,Order(u)); SetIsTame(result,true);
    SetBaseRoot(result,result); SetPowerOverBaseRoot(result,1);
    SetFactorizationIntoCSCRCT(result,[result]);

    latex := ValueOption("LaTeXString");
    if latex = fail then
      if IsOne(m) then
        SetLaTeXString(result,Concatenation("\\rho_{",String(u),"}"));
      else
        SetLaTeXString(result,Concatenation("\\rho_{",String(r),"(",
                                            String(m),"),",String(u),"}"));
      fi;
    elif not IsEmpty(latex) then SetLaTeXString(result,latex); fi;

    return result;
  end );

#############################################################################
##
#F  ClassRotationOfZxZ( ... ) . . . . . . . . . . . . . class rotation of Z^2
##
##  This function is called by `ClassRotation' if the first argument is
##  either Integers^2, a row vector of length 2 with integer entries or
##  a residue class of Integers^2. For recognized arguments, see there.
##
InstallGlobalFunction( ClassRotationOfZxZ,

  function ( arg )

    local  result, R, mats, r, m, u, uimg, M, U, Uimg, cl,
           coeff, idcoeff, res, pos, latex;

    if Length(arg) = 1 and IsList(arg[1]) then arg := arg[1]; fi;

    R := Integers^2; mats := FullMatrixAlgebra(Integers,2);

    u := arg[Length(arg)]; arg := arg{[1..Length(arg)-1]};
    if IsZxZ(arg[1]) then arg := arg{[2..Length(arg)]}; fi;

    if   not u in mats or not DeterminantMat(u) in [-1,1]
      or not Length(arg) in [0..2]
      or Length(arg) = 1 and not IsResidueClassOfZxZ(arg[1])
      or Length(arg) = 2 and not (arg[1] in R and arg[2] in mats)
    then Error("usage: see ?ClassRotation( r, m, u )\n"); fi;

    if   IsOne(u) then return IdentityRcwaMappingOfZxZ; fi;

    if   arg = [] then cl := R;
    elif Length(arg) = 1 then cl := arg[1];
    else cl := ResidueClass(arg[1],arg[2]); fi;

    r := Residue(cl); m := Modulus(cl);

    res     := AllResidues(R,m);
    idcoeff := [[[1,0],[0,1]],[0,0],1];
    coeff   := ListWithIdenticalEntries(Length(res),idcoeff);

    M := NullMat(3,3);
    M{[1..2]}{[1..2]} := m;
    M[3][3] := 1;
    M[3]{[1..2]} := r;

    U := NullMat(3,3);
    U{[1..2]}{[1..2]} := u;
    U[3][3] := 1;

    Uimg := U^M;
    Uimg := Uimg * Lcm(List(Flat(Uimg),DenominatorRat));
    uimg := Uimg{[1..2]}{[1..2]};

    pos        := PositionSorted(res,r);
    coeff[pos] := [uimg,Uimg[3]{[1..2]},Uimg[3][3]];

    result     := RcwaMapping(R,m,coeff);

    SetIsClassRotation(result,true);
    SetRotationFactor(result,u);
    if IsOne(-u) then SetIsClassReflection(result,true); fi;
    SetIsBijective(result,true);
    SetOrder(result,Order(u));
    SetIsTame(result,true);
    SetBaseRoot(result,result); SetPowerOverBaseRoot(result,1);
    SetFactorizationIntoCSCRCT(result,[result]);

    latex := ValueOption("LaTeXString");
    if latex = fail then
      latex := Concatenation("\\rho_{",ViewString(cl),
                             ",",BlankFreeString(u),"}");
      latex := ReplacedString(latex,"Z","\\mathbb{Z}");
      SetLaTeXString(result,latex);
    elif not IsEmpty(latex) then SetLaTeXString(result,latex); fi;

    return result;
  end );

#############################################################################
##
#M  IsClassRotation( <sigma> ) . . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( IsClassRotation,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( sigma )

    local  S, u, c;

    S := Union(Support(sigma),ExcludedElements(Support(sigma)));
    if not IsResidueClass(S) then return false; fi;
    c := First(Coefficients(sigma),c->not IsOne(c[1]));
    if c = fail then return false; else u := c[1]; fi;
    if sigma = ClassRotation(S,u) then
      SetRotationFactor(sigma,u);
      return true;
    else return false; fi;
  end );

#############################################################################
##
#M  IsClassRotation( <sigma> ) . . . . . . . . . . . .  for class reflections
##
InstallTrueMethod( IsClassRotation, IsClassReflection );

#############################################################################
##
#M  String( <cr> ) . . . . . . . . . . . . . . . . . . .  for class rotations
#M  ViewString( <cr> ) . . . . . . . . . . . . . . . . .  for class rotations
#M  PrintObj( <cr> ) . . . . . . . . . . . . . . . . . .  for class rotations
#M  ViewObj( <cr> )  . . . . . . . . . . . . . . . . . .  for class rotations
##
InstallMethod( String, "for class rotations (RCWA)", true,
               [ IsRcwaMapping and IsClassRotation ], SUM_FLAGS-10,
               cr -> Concatenation(List(["ClassRotation(",Source(cr),",",
                                         Residue(Support(cr)),",",
                                         Modulus(Support(cr)),",",
                                         RotationFactor(cr),")"],
                                        BlankFreeString)));

InstallMethod( ViewString, "for class rotations (RCWA)", true,
               [ IsRcwaMapping and IsClassRotation ], SUM_FLAGS-10,

  function ( cr )

    local  cl, name, suppname;

    if   ValueOption("PrintNotation") = true
    then return String(cr); fi;
    if   ValueOption("AbridgedNotation") = true
    then name := "cr"; else name := "ClassRotation"; fi;
    cl := Union(Support(cr:BeQuiet),ExcludedElements(Support(cr)));
    if IsRing(cl) or IsZxZ(cl) then suppname := RingToString(cl);
                               else suppname := ViewString(cl); fi;
    return Concatenation(List([name,"( ",suppname,", ",
                               RotationFactor(cr)," )"],String));
  end );

InstallMethod( PrintObj, "for class rotations (RCWA)", true,
               [ IsRcwaMapping and IsClassRotation ], SUM_FLAGS+10,
               function ( cr ) Print( String( cr ) ); end );

InstallMethod( ViewObj, "for class rotations (RCWA)", true,
               [ IsRcwaMapping and IsClassRotation ], 20,
               function ( cr ) Print( ViewString( cr ) ); end );

#############################################################################
##
#F  ClassTransposition( <R>, <r1>, <m1>, <r2>, <m2> ) . . class transposition
#F  ClassTransposition( <r1>, <m1>, <r2>, <m2> )            tau_r1(m1),r2(m2)
#F  ClassTransposition( <R>, <cl1>, <cl2> ) . . . dito, cl1=r1(m1) cl2=r2(m2)
#F  ClassTransposition( <cl1>, <cl2> )  . . . . . . . . . . . . . . .  (dito)
##
##  (Enclosing the argument list in list brackets is permitted.)
##
InstallGlobalFunction( ClassTransposition,

  function ( arg )

    local  result, is_usual_ct, type, R, r1, m1, r2, m2, cl1, cl2, h, latex;

    if Length(arg) = 1 and IsList(arg[1]) then arg := arg[1]; fi;

    if   IsZxZ(arg[1])
      or IsRowVector(arg[1]) and Length(arg[1]) = 2 and ForAll(arg[1],IsInt)
      or IsResidueClassOfZxZ(arg[1])
    then return CallFuncList(ClassTranspositionOfZxZ,arg); fi;

    if not Length(arg) in [2..5]
      or     Length(arg) = 2 and not (ForAll(arg,IsResidueClass)
                                   or ForAll(arg,IsResidueClassWithFixedRep))
      or     Length(arg) = 3
         and not (     IsRing(arg[1]) and ForAll(arg{[2,3]},IsResidueClass)
                   and arg[1] = UnderlyingRing(FamilyObj(arg[2]))
                   and arg[1] = UnderlyingRing(FamilyObj(arg[3])))
      or     Length(arg) = 4 and not ForAll(arg,IsRingElement)
      or     Length(arg) = 5 and not (    IsRing(arg[1])
                                      and IsSubset(arg[1],arg{[2..5]}))
    then Error("usage: see ?ClassTransposition( r1, m1, r2, m2 )\n"); fi;

    if IsRing(arg[1]) then R := arg[1]; arg := arg{[2..Length(arg)]}; fi;
    if   IsResidueClass(arg[1]) or IsResidueClassWithFixedRep(arg[1])
    then if not IsBound(R) then R := UnderlyingRing(FamilyObj(arg[1])); fi;
         arg := [Residue(arg[1]),Modulus(arg[1]),
                 Residue(arg[2]),Modulus(arg[2])] * One(R);
    elif not IsBound(R) then R := DefaultRing(arg{[2,4]}); fi;
    arg := arg * One(R); # Now we know R, and we have arg = [r1,m1,r2,m2].

    r1 := arg[1]; m1 := arg[2]; r2 := arg[3]; m2 := arg[4];

    if IsZero(m1*m2) or IsZero((r1-r2) mod Gcd(R,m1,m2)) then
      Error("ClassTransposition: The residue classes must be disjoint.\n");
    fi;

    is_usual_ct := m1 = StandardAssociate(R,m1)
               and m2 = StandardAssociate(R,m2)
               and r1 mod m1 = r1 and r2 mod m2 = r2;

    if   [m1,r1] > [m2,r2]
    then h := r1; r1 := r2; r2 := h; h := m1; m1 := m2; m2 := h; fi;

    if is_usual_ct then
      cl1 := ResidueClass(R,m1,r1);
      cl2 := ResidueClass(R,m2,r2);
    else
      cl1 := ResidueClassWithFixedRepresentative(R,m1,r1);
      cl2 := ResidueClassWithFixedRepresentative(R,m2,r2);
    fi;

    result := RcwaMapping([[cl1,cl2]]);
    if IsRcwaMappingOfZ(result)
      and IsBoundGlobal("CTSparse") and ValueGlobal("CTSparse") = true
    then
      result := SparseRepresentation(result);
    fi;

    if is_usual_ct then SetIsClassTransposition(result,true); fi;
    SetIsGeneralizedClassTransposition(result,true);
    SetTransposedClasses(result,[cl1,cl2]);

    latex := ValueOption("LaTeXString");
    if latex = fail then
      if IsIntegers(R) and [m1,m2] = [2,2] then
        SetLaTeXString(result,"\\tau");
      else
        SetLaTeXString(result,Concatenation("\\tau_{",
                                            String(r1),"(",String(m1),"),",
                                            String(r2),"(",String(m2),")}"));
      fi;
    elif not IsEmpty(latex) then SetLaTeXString(result,latex); fi;

    if is_usual_ct then SetFactorizationIntoCSCRCT(result,[result]); fi;

    return result;
  end );

#############################################################################
##
#F  ClassTranspositionOfZxZ( ... ) . . . . . . . . class transposition of Z^2
##
##  This function is called by `ClassTransposition' if the first argument
##  is either Integers^2, a row vector of length 2 with integer entries
##  or a residue class of Integers^2. For recognized arguments, see there.
##
InstallGlobalFunction( ClassTranspositionOfZxZ,

  function ( arg )

    local  result, R, M, r1, m1, r2, m2, cl1, cl2, h, latex;

    if Length(arg) = 1 and IsList(arg[1]) then arg := arg[1]; fi;

    R := Integers^2; M := FullMatrixAlgebra(Integers,2);

    if not Length(arg) in [2..5]
      or     Length(arg) = 2 and not ForAll(arg,IsResidueClassOfZxZ)
      or     Length(arg) = 3 and not (IsZxZ(arg[1]) 
                                  and ForAll(arg{[2,3]},IsResidueClassOfZxZ))
      or     Length(arg) = 4 and not ( arg[1] in R and arg[2] in M
                                   and arg[3] in R and arg[4] in M )
      or     Length(arg) = 5 and not ( IsZxZ(arg[1])
                                   and arg[2] in R and arg[3] in M
                                   and arg[4] in R and arg[5] in M )
    then Error("usage: see ?ClassTransposition( r1, m1, r2, m2 )\n"); fi;

    if IsZxZ(arg[1]) then arg := arg{[2..Length(arg)]}; fi;
    if IsResidueClass(arg[1]) then
      arg := [Residue(arg[1]),Modulus(arg[1]),
              Residue(arg[2]),Modulus(arg[2])];
    fi; # Now we have arg = [r1,m1,r2,m2].

    r1 := arg[1]; m1 := arg[2]; r2 := arg[3]; m2 := arg[4];

    if   [m1,r1] > [m2,r2]
    then h := r1; r1 := r2; r2 := h; h := m1; m1 := m2; m2 := h; fi;

    if DeterminantMat(m1*m2) = 0 then
      Error("ClassTransposition:\n",
            "The moduli of the residue classes must be invertible.\n");
    fi;

    cl1 := ResidueClass(R,m1,r1);
    cl2 := ResidueClass(R,m2,r2);

    if Intersection(cl1,cl2) <> [] then
      Error("ClassTransposition: The residue classes must be disjoint.\n");
    fi;

    result := RcwaMapping([[cl1,cl2]]);

    SetIsClassTransposition(result,true);
    SetIsGeneralizedClassTransposition(result,true);
    SetTransposedClasses(result,[cl1,cl2]);

    latex := ValueOption("LaTeXString");
    if latex = fail then
      latex := Concatenation("\\tau_{",ViewString(cl1),",",
                                       ViewString(cl2),"}");
      latex := ReplacedString(latex,"Z","\\mathbb{Z}");
      SetLaTeXString(result,latex);
    elif not IsEmpty(latex) then SetLaTeXString(result,latex); fi;

    SetFactorizationIntoCSCRCT(result,[result]);

    return result;
  end );

#############################################################################
##
#M  IsClassTransposition( <sigma> ) . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( IsClassTransposition,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( sigma )

    local  cls;

    if IsOne(sigma) then return false; fi;
    if not IsBijective(sigma) then return false; fi;
    if HasOrder(sigma) and Order(sigma) <> 2 then return false; fi;
    if   IsRcwaMappingStandardRep(sigma)
     and Length(Set(Coefficients(sigma))) > 3
    then return false; fi;
    if   IsRcwaMappingSparseRep(sigma)
     and Length(Set(Coefficients(sigma),c->c{[3..5]})) > 3
    then return false; fi;
    cls := AsUnionOfFewClasses(Support(sigma));
    if Length(cls) = 1 then cls := SplittedClass(cls[1],2); fi;
    if Length(cls) > 2 then return false; fi;
    if   sigma = ClassTransposition(cls)
    then SetTransposedClasses(sigma,cls);
         SetIsGeneralizedClassTransposition(sigma,true);
         return true;
    else return false; fi;
  end );

#############################################################################
##
#M  IsClassTransposition( <sigma> ) . . . . . . . .  for rcwa mappings of Z^2
##
InstallMethod( IsClassTransposition,
               "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZ ], 0,

  function ( sigma )

    local  cls, split;

    if IsOne(sigma) then return false; fi;
    if Length(Set(Coefficients(sigma))) > 3 then return false; fi;
    cls := AsUnionOfFewClasses(Support(sigma:BeQuiet));
    if   Length(cls) = 1 then
      for split in List([[2,1],[1,2]],v->SplittedClass(cls[1],v)) do
        if sigma = ClassTransposition(split) then
          SetTransposedClasses(sigma,split);
          SetIsGeneralizedClassTransposition(sigma,true); return true;
        fi;
      od;
      return false;
    elif Length(cls) = 2 then
      if sigma = ClassTransposition(cls) then
        SetTransposedClasses(sigma,cls);
        SetIsGeneralizedClassTransposition(sigma,true); return true;
      fi;
    else return false; fi;
  end );

#############################################################################
##
#M  IsGeneralizedClassTransposition( <sigma> ) . . . . . .  for rcwa mappings
##
InstallMethod( IsGeneralizedClassTransposition,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( sigma )

    local  cls, cls_fixedrep, affsrc, r1, m1, r2, m2;

    if   HasIsClassTransposition(sigma) and IsClassTransposition(sigma)
    then return true; fi;
    if IsOne(sigma) or not IsBijective(sigma)
                    or Length(Set(Coefficients(sigma))) > 3
    then return false; fi;
    affsrc := LargestSourcesOfAffineMappings(sigma);
    if Length(affsrc) > 3 then return false; fi;
    cls := Filtered(affsrc,cl->IsResidueClass(cl)
                           and IsSubset(Support(sigma),cl));
    if Length(cls) <> 2 then return false; fi;
    if Permutation(sigma,cls) = (1,2) then
      m1 := Modulus(cls[1]); r1 := Residue(cls[1]);
      m2 := Modulus(cls[2]); r2 := r1^sigma;
      if not IsClassWiseOrderPreserving(sigma) then m2 := -m2; fi;
      cls_fixedrep := [ ResidueClassWithFixedRep(Source(sigma),m1,r1),
                        ResidueClassWithFixedRep(Source(sigma),m2,r2) ];
      Assert(4,sigma=ClassTransposition(cls_fixedrep));
      SetTransposedClasses(sigma,cls_fixedrep);
      return true;
    else return false; fi;
  end );

#############################################################################
##
#M  TransposedClasses( <sigma> ) . . . . . . . . . . for class transpositions
##
InstallMethod( TransposedClasses,
               "for class transpositions (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( ct )
    if   IsClassTransposition(ct) or IsGeneralizedClassTransposition(ct)
    then return TransposedClasses(ct);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  String( <ct> ) . . . . . . . . . . . . . . . . . for class transpositions
#M  ViewString( <ct> ) . . . . . . . . . . . . . . . for class transpositions
#M  PrintObj( <ct> ) . . . . . . . . . . . . . . . . for class transpositions
#M  ViewObj( <ct> )  . . . . . . . . . . . . . . . . for class transpositions
##
InstallMethod( String, "for class transpositions (RCWA)", true,
               [ IsRcwaMapping and IsGeneralizedClassTransposition ],
               SUM_FLAGS,

  function ( ct )

    local  type, cls, str;

    cls := TransposedClasses(ct);
    if   ForAll(cls,IsResidueClass)
    then type := "ClassTransposition(";
    else type := "GeneralizedClassTransposition("; fi;
    if IsRcwaMappingOfZ(ct) then
      str := Concatenation(List([type,
                                 Residue(cls[1]),",",Modulus(cls[1]),",",
                                 Residue(cls[2]),",",Modulus(cls[2]),")"],
                                BlankFreeString));
    else
      str := Concatenation(List([type,Source(ct),",",
                                 Residue(cls[1]),",",Modulus(cls[1]),",",
                                 Residue(cls[2]),",",Modulus(cls[2]),")"],
                                BlankFreeString));
    fi;
    return BlankFreeString(str);
  end );

InstallMethod( ViewString, "for class transpositions (RCWA)", true,
               [ IsRcwaMapping and IsGeneralizedClassTransposition ],
               SUM_FLAGS,

  function ( ct )

    local  cls, name;

    if ValueOption("PrintNotation") = true then return String(ct); fi;

    cls := TransposedClasses(ct);
    if   ForAll(cls,IsResidueClass)
    then name := "ClassTransposition";
    else name := "GeneralizedClassTransposition"; fi;
    if    ValueOption("CycleNotation") <> false
      and ValueOption("AbridgedNotation") <> false
    then return Filtered(Concatenation(List(["( ",cls[1],", ",
                                                  cls[2]," )"],
                                             ViewString)),ch->ch<>'\"');
    else return Filtered(Concatenation(List([name,"( ",cls[1],", ",
                                                       cls[2]," )"],
                                             ViewString)),ch->ch<>'\"');
    fi;

  end );

InstallMethod( PrintObj, "for class transpositions (RCWA)", true,
               [ IsRcwaMapping and IsGeneralizedClassTransposition ],
               SUM_FLAGS+10, function ( ct ) Print( String( ct ) ); end );

InstallMethod( ViewObj, "for class transpositions (RCWA)", true,
               [ IsRcwaMapping and IsGeneralizedClassTransposition ], 20,
               function ( ct ) Print( ViewString( ct ) ); end );

#############################################################################
##
#M  SplittedClassTransposition( <ct>, <k> ) . . . . . . .  2-argument version
##
InstallMethod( SplittedClassTransposition,
               "default method (RCWA)", ReturnTrue,
               [ IsRcwaMapping and IsClassTransposition, IsObject ], 0,
               function ( ct, k )
                 return SplittedClassTransposition(ct,k,false);
               end );

#############################################################################
##
#M  SplittedClassTransposition( <ct>, <k>, <cross> ) . . . 3-argument version
##
InstallMethod( SplittedClassTransposition,
               "for a class transposition (RCWA)", ReturnTrue,
               [ IsRcwaMapping and IsClassTransposition,
                 IsObject, IsBool ], 0,

  function ( ct, k, cross )

    local  cls, pairs;

    if IsZero(k) or not k in Source(ct) then TryNextMethod(); fi;
    cls := List(TransposedClasses(ct),cl->SplittedClass(cl,k));
    if cross then pairs := Cartesian(cls);
             else pairs := TransposedMat(cls); fi;
    return List(pairs,ClassTransposition);
  end );

#############################################################################
##
#F  ClassPairs( [ <P> ], <m> )
#F  ClassPairs( [ <R> ], <m> )
##
##  In the one-argument version, this function returns a list of all
##  unordered pairs of disjoint residue classes of Z with modulus <= <m>.
##  If the option "divisors" is set, the list contains only those pairs of
##  residue classes where the moduli divide <m>.
##
##  In the two-argument version, if <P> is a set of primes, the function
##  returns a list of all unordered pairs of disjoint residue classes of Z
##  whose moduli are less than or equal to <m> and factor completely
##  over <P>.
##
##  If <R> is a ring, the function does the following:
##
##    - If <R> is either the ring of integers or a semilocalization thereof,
##      it returns a list of all unordered pairs of disjoint residue classes
##      of <R> with modulus <= <m>.
##
##    - If <R> is a univariate polynomial ring over a finite field, it
##      returns a list of all unordered pairs of disjoint residue classes
##      of <R> whose moduli have degree less than <m>.
##
##    - If <R> is Integers^2, it returns a list of all unordered pairs of
##      disjoint residue classes whose moduli have determinant at most <m>.
##
##  The purpose of this function is to generate a list of all
##  class transpositions whose moduli do not exceed a given bound.
##  For reasons of saving time or memory, it may return pairs of
##  residue classes [r1(m1),r2(m2)] in the form of 4-tuples [r1,m1,r2,m2]
##  of ring elements. Regardless of whether it does so or not, one can
##  always obtain the corresponding list of class transpositions by
##  List( ClassPairs( <R>, <m> ), ClassTransposition );
##
InstallGlobalFunction( ClassPairs,

  function ( arg )

    local  R, P, m, tuples, moduli, Degree, classes,
           m1, r1, m2, r2, d, i, j, usage;

    usage := "usage: ClassPairs( [ <R> | <P> ], <m> )\n";

    if Length(arg) = 1 then
      m := arg[1];
      if IsInt(m) then R := Integers; else R := DefaultRing(m); fi;
    elif Length(arg) = 2 then
      if IsRing(arg[1]) or IsZxZ(arg[1]) then
        R := arg[1];
      elif IsList(arg[1]) and ForAll(arg[1],p->IsPosInt(p) and IsPrime(p))
      then R := Integers; P := arg[1];
      else Error(usage); return fail; fi;
      m := arg[2];
    else Error(usage); return fail; fi;

    if IsIntegers(R) or IsZ_pi(R) then
      tuples := [];
      if ValueOption("divisors") = true then
        moduli := Difference(DivisorsInt(m),[1]);
      elif IsBound(P) then
        moduli := Difference(AllSmoothIntegers(P,m),[1]);
      else
        moduli := [2..m];
      fi;
      for i in [1..Length(moduli)] do
        m2 := moduli[i];
        for j in [1..i] do
          m1 := moduli[j];
          d := Gcd(m1,m2);
          for r1 in [0..m1-1] do
            for r2 in [0..m2-1] do
              if m1 = m2 and r1 > r2 then continue; fi;
              if (r1 - r2) mod d <> 0 then
                Add(tuples,[r1,m1,r2,m2]);
              fi;
            od;
          od;
        od;
      od;
      tuples := Set(tuples);
      if IsZ_pi(R) then
        tuples := Filtered(tuples,t->IsSubset(NoninvertiblePrimes(R),
                                              Factors(t[2]*t[4])));
      fi;
    elif     IsUnivariatePolynomialRing(R) and IsField(LeftActingDomain(R))
         and IsFinite(LeftActingDomain(R))
    then
      Degree := DegreeOfUnivariateLaurentPolynomial;
      tuples := [];
      moduli := Filtered(AllResidues(R,m),r->IsPosInt(Degree(r)));
      for m1 in moduli do
        for m2 in moduli do
          if m1 > m2 then continue; fi;
          for r1 in AllResidues(R,m1) do
            for r2 in AllResidues(R,m2) do
              if (m1 <> m2 or r1 < r2) and not IsZero((r1-r2) mod Gcd(m1,m2))
              then Add(tuples,[r1,m1,r2,m2]); fi;
            od;
          od;
        od;
      od;
    elif IsZxZ(R) then
      moduli  := All2x2IntegerMatricesInHNFWithDeterminantUpTo(m);
      classes := Concatenation(List(moduli,m->AllResidueClassesModulo(R,m)));
      tuples  := Filtered(Combinations(classes,2),
                          t->Intersection(t[1],t[2])=[]);
    else
      Error("ClassPairs: Sorry, the ring ",R,"\n",String(" ",19),
            "is currently not supported by this function.\n");
    fi;
    return tuples;
  end );

InstallValue( CLASS_PAIRS, [ 6, ClassPairs(6) ] );
InstallValue( CLASS_PAIRS_LARGE, CLASS_PAIRS );

#############################################################################
##
#F  NumberClassPairs( <m> ) . . compute Length( ClassPairs( m ) ) efficiently
#F  NrClassPairs( <m> )
##
InstallGlobalFunction( NumberClassPairs,

  function ( m )

    local  nr, coprimes, m1, m2, modlist, mods, d;

    if not IsPosInt( m ) then Error("usage: NrClassPairs( <m> )\n"); fi;

    coprimes := Union([[1,1]],Filtered(Combinations([1..Int(m/2)],2),
                                       t->Gcd(t) = 1));
    nr := 0;
    for d in [2..m] do
      modlist := Filtered(d*coprimes,mods->Maximum(mods)<=m);
      for mods in modlist do
        m1 := mods[1]; m2 := mods[2];
        if m1 = m2 then nr := nr + m1 * (m1 - 1)/2;
                   else nr := nr + (d - 1)/d * m1 * m2;
        fi;
      od;
    od;

    return nr;  
  end );

#############################################################################
##
#M  PrimeSwitch( <p> ) . . . . . . . . . . . . . . .  for an odd prime number
##
InstallMethod( PrimeSwitch,
               "for an odd prime number (RCWA)",  true, [ IsPosInt ], 0,

  function ( p )
    if   p = 2 or not IsPrimeInt(p)
    then Error("PrimeSwitch( <p> ): <p> must be an odd prime\n"); fi;
    return PrimeSwitch(p,1);
  end );

#############################################################################
##
#M  PrimeSwitch( <p>, <k> ) .  for an odd prime number and a positive integer
##
InstallMethod( PrimeSwitch,
               "for an odd prime number and a positive integer (RCWA)", 
               ReturnTrue, [ IsPosInt, IsPosInt ], 0,

  function ( p, k )

    local  result, facts, kstr, latex;

    if   p = 2 or not IsPrimeInt(p)
    then Error("PrimeSwitch( <p>, <k> ): <p> must be an odd prime\n"); fi;
    facts := List([[k,2*k*p,0,8*k],[2*k*p-k,2*k*p,4*k,8*k],
                   [0,4*k,k,2*k*p],[2*k,4*k,2*k*p-k,2*k*p],
                   [2*k,2*k*p,k,4*k*p],[4*k,2*k*p,2*k*p+k,4*k*p]],
                  ClassTransposition);
    result := Product(facts); SetIsPrimeSwitch(result,true);
    SetIsTame(result,false); SetOrder(result,infinity);
    SetBaseRoot(result,result); SetPowerOverBaseRoot(result,1);
    SetFactorizationIntoCSCRCT(result,facts);
    SetFactorizationIntoCSCRCT(result^-1,Reversed(facts));
    latex := ValueOption("LaTeXString");
    if latex = fail then
      if k=1 then kstr := ""; else kstr := Concatenation(",",String(k)); fi;
      SetLaTeXString(result,Concatenation("\\sigma_{",String(p),kstr,"}"));
    elif not IsEmpty(latex) then SetLaTeXString(result,latex); fi;
    return result;
  end );

#############################################################################
##
#M  PrimeSwitch( <p>, <r>, <m> ) .  for odd prime number, residue and modulus 
##
InstallMethod( PrimeSwitch,
               "for an odd prime number, a residue and a modulus (RCWA)", 
               ReturnTrue, [ IsPosInt, IsInt, IsPosInt ], 0,

  function ( p, r, m )

    local  result, facts, mp, r1, r2, rc, latex;

    if p = 2 or not IsPrimeInt(p) or m mod 4 <> 0 then
      Error("PrimeSwitch( <p>, <r>, <m> ): <p> must be an odd prime ",
            "and <m> must be\na multiple of 4\n");
      return fail;
    fi;

    r := r mod m; r1 := 1 - r mod 2;
    if r < m/2 then r2 := r+m/2; else r2 := r-m/2; fi;
    facts := List([[r1,m/2,r2,m],[r2,m,r1,p*m/2],[r mod (m/2),m/2,r1,p*m/2]],
                  ClassTransposition);
    result := Product(facts);

    SetIsPrimeSwitch(result,true);
    SetIsTame(result,false); SetOrder(result,infinity);
    SetBaseRoot(result,result); SetPowerOverBaseRoot(result,1);
    SetFactorizationIntoCSCRCT(result,facts);
    SetFactorizationIntoCSCRCT(result^-1,Reversed(facts));
    latex := ValueOption("LaTeXString");
    if latex = fail then
      SetLaTeXString(result,Concatenation("\\sigma_{",String(p),",",
                                          String(r),"(",String(m),")}"));
    elif not IsEmpty(latex) then SetLaTeXString(result,latex); fi;

    return result;
  end );

#############################################################################
##
#M  PrimeSwitch( <p>, <cl> ) . .  for an odd prime number and a residue class
##
InstallMethod( PrimeSwitch,
               "for an odd prime number and a residue class (RCWA)", 
               ReturnTrue, [ IsPosInt, IsUnionOfResidueClassesOfZ ], 0,

  function ( p, cl )
    if   p = 2 or not IsPrimeInt(p)
    then Error("PrimeSwitch( <p>, <cl> ): <p> must be an odd prime\n"); fi;
    if not IsResidueClass(cl) then TryNextMethod(); fi;
    return PrimeSwitch(p,Residue(cl),Mod(cl));
  end );

#############################################################################
##
#M  IsPrimeSwitch( <g> ) . . . . . . . . . . . . . . . for rcwa mappings of Z
##
InstallMethod( IsPrimeSwitch,
               "for rcwa mappings of Z (RCWA)", 
               true, [ IsRcwaMappingOfZ ], 0,

  function ( g )

    local  p, cl, k;

    if not IsBijective(g) or not IsSignPreserving(g) then return false; fi;
    p := Maximum(Factors(Mult(g)));
    if Mult(g) <> p or Div(g) <> 2 then return false; fi;
    cl := Multpk(g,p,1);
    if not IsResidueClass(cl) then return false; fi;
    k := Mod(cl)/4;
    if IsInt(k) and g = PrimeSwitch(p,k) then return true; fi;
    return g = PrimeSwitch(p,cl);
  end );

#############################################################################
##
#M  String( <sigma_p> ) . . . . . . . . . . . . . . . . .  for prime switches
#M  ViewString( <sigma_p> ) . . . . . . . . . . . . . . .  for prime switches
#M  PrintObj( <sigma_p> ) . . . . . . . . . . . . . . . .  for prime switches
#M  ViewObj( <sigma_p> )  . . . . . . . . . . . . . . . .  for prime switches
##
InstallMethod( String, "for prime switches (RCWA)", true,
               [ IsRcwaMapping and IsPrimeSwitch ], SUM_FLAGS,

  function ( sigma_p )

    local  p, k, kstr, cl;

    p := Maximum(Factors(Multiplier(sigma_p)));
    k := 1/(4*Density(Multpk(sigma_p,p,1)));
    if IsInt(k) and sigma_p = PrimeSwitch(p,k) then
      if k = 1 then kstr := "";
               else kstr := Concatenation(",",String(k)); fi;
      return Concatenation("PrimeSwitch(",String(p),kstr,")");
    else
      cl := Multpk(sigma_p,p,1);
      if sigma_p = PrimeSwitch(p,cl) then
        return Concatenation("PrimeSwitch(",String(p),",",
                             String(Residue(cl)),",",String(Mod(cl)),")");
      else return fail; fi;
    fi;
  end );

InstallMethod( ViewString, "for prime switches (RCWA)", true,
               [ IsRcwaMapping and IsPrimeSwitch ], SUM_FLAGS,

  function ( ps )

    local  name;

    if   ValueOption("PrintNotation") = true
    then return String(ps); fi;
    if   ValueOption("AbridgedNotation") = true
    then name := "ps"; else name := "PrimeSwitch"; fi;
    return ReplacedString(String(ps),"PrimeSwitch",name);
  end );

InstallMethod( PrintObj, "for prime switches (RCWA)", true,
               [ IsRcwaMapping and IsPrimeSwitch ], SUM_FLAGS+10,
               function ( sigma_p ) Print( String( sigma_p ) ); end );

InstallMethod( ViewObj, "for prime switches (RCWA)", true,
               [ IsRcwaMapping and IsPrimeSwitch ], 20,
               function ( sigma_p ) Print( ViewString( sigma_p ) ); end );

#############################################################################
##
#F  mKnot( <m> ) . . . . . .  an rcwa permutation of Timothy P. Keller's type
##
InstallGlobalFunction ( mKnot,

  function ( m )

    local  result;

    if   not IsPosInt(m) or m mod 2 <> 1 or m = 1
    then Error("usage: see ?mKnot( m )\n"); fi;
    result := RcwaMapping(List([0..m-1],r->[m+(-1)^r,(-1)^(r+1)*r,m]));
    SetIsBijective(result,true);
    SetIsTame(result,false); SetOrder(result,infinity);
    SetName(result,Concatenation("mKnot(",String(m),")"));
    SetLaTeXString(result,Concatenation("\\kappa_{",String(m),"}"));
    return result;
  end );

#############################################################################
##
#F  ClassUnionShift( <S> ) . . . . . shift of rc.-union <S> by Modulus( <S> )
##
InstallGlobalFunction( ClassUnionShift,

  function ( S )

    local  R, m, res, resS, r, c, f;

    R := UnderlyingRing(FamilyObj(S));
    m := Modulus(S); resS := Residues(S); res := AllResidues(R,m);
    c := List(res,r->[1,0,1]*One(R));
    for r in resS do c[PositionSorted(res,r)] := [1,m,1]*One(R); od;
    return RcwaMapping(R,m,c);
  end );

#############################################################################
##
#S  Methods for `String', `Print', `View', `Display' and `LaTeX'. ///////////
##
#############################################################################

#############################################################################
##
#M  String( <f> ) . . . . . . . . . . . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( String,
               "for rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ ], 0,

  function ( arg )

    local f, lng, s;

    f := arg[1]; if Length(arg) > 1 then lng := arg[2]; fi;
    s := Concatenation( "RcwaMapping( ", String( Coefficients(f) ), " )" );
    if IsBound(lng) then s := String(s,lng); fi;
    return s;
  end );

#############################################################################
##
#M  String( <f> ) . . . . . . . . . . . . . . . . .  for rcwa mappings of Z^2
##
InstallMethod( String,
               "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZInStandardRep ], 0,

  function ( arg )

    local f, lng, s;

    f := arg[1]; if Length(arg) > 1 then lng := arg[2]; fi;
    s := Concatenation( "RcwaMapping( Integers^2, ", String( Modulus(f) ),
                        ", ", String( Coefficients(f) ), " )" );
    if IsBound(lng) then s := String(s,lng); fi;
    return s;
  end );

#############################################################################
##
#M  String( <f> ) . . . . . . . . . . . . . . . . for rcwa mappings of Z_(pi)
##
InstallMethod( String,
               "for rcwa mappings of Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZ_piInStandardRep ], 0,

  function ( arg )

    local  f, lng, s;

    f := arg[1]; if Length(arg) > 1 then lng := arg[2]; fi;
    s := Concatenation( "RcwaMapping( ",
                        String(NoninvertiblePrimes(Source(f))), ", ",
                        String(Coefficients(f)), " )" );
    if IsBound(lng) then s := String(s,lng); fi;
    return s;
  end );

#############################################################################
##
#M  String( <f> ) . . . . . . . . . . . . . . . for rcwa mappings of GF(q)[x]
##
InstallMethod( String,
               "for rcwa mappings of GF(q)[x] (RCWA)",
               true, [ IsRcwaMappingOfGFqxInStandardRep ], 0,

  function ( arg )

    local  f, lng, s;

    f := arg[1]; if Length(arg) > 1 then lng := arg[2]; fi;
    s := Concatenation( "RcwaMapping( ",
                        String(Size(UnderlyingField(f))), ", ",
                        String(Modulus(f)), ", ",
                        String(Coefficients(f)), " )" );
    if IsBound(lng) then s := String(s,lng); fi;
    return s;
  end );

#############################################################################
##
#M  String( <f> ) . . . . . . . . . . . . .  for rcwa mappings with base root
#M  ViewString( <f> ) . . . . . . . . . . .  for rcwa mappings with base root
##
InstallMethod( String, "for rcwa mappings with base root (RCWA)", true,
               [ IsRcwaMapping and HasBaseRoot ], 20,
               f -> Concatenation(String(BaseRoot(f)),"^",
                                  String(PowerOverBaseRoot(f))) );

InstallMethod( ViewString, "for rcwa mappings with base root (RCWA)", true,
               [ IsRcwaMapping and HasBaseRoot ], 0,
               f -> Concatenation(ViewString(BaseRoot(f)),"^",
                                  String(PowerOverBaseRoot(f))) );

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( PrintObj,
               "for rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ ], SUM_FLAGS,

  function ( f )
    Print( "RcwaMapping( ", Coefficients(f), " )" );
  end );

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . . . . . .  for rcwa mappings of Z^2
##
InstallMethod( PrintObj,
               "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZInStandardRep ], SUM_FLAGS,

  function ( f )
    Print( "RcwaMapping( Integers^2, ",
                         Modulus(f), ", ", Coefficients(f), " )" );
  end );

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . . . . . for rcwa mappings of Z_(pi)
##
InstallMethod( PrintObj,
               "for rcwa mappings of Z_(pi) (RCWA)", true,
               [ IsRcwaMappingOfZ_piInStandardRep ],  SUM_FLAGS,

  function ( f )
    Print( "RcwaMapping( ",
           NoninvertiblePrimes(Source(f)), ", ", Coefficients(f), " )" );
  end );

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . . . . for rcwa mappings of GF(q)[x]
##
InstallMethod( PrintObj,
               "for rcwa mappings of GF(q)[x] (RCWA)", true,
               [ IsRcwaMappingOfGFqxInStandardRep ], SUM_FLAGS,

  function ( f )
    Print( "RcwaMapping( ", Size(UnderlyingField(f)),
           ", ", Modulus(f), ", ", Coefficients(f), " )" );
  end );

#############################################################################
##
#M  ViewObj( <f> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( ViewObj,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  cycles, cyclenotation, i, j;

    if IsZero(f) or IsOne(f) then View(f); return; fi;
    if HasBaseRoot(f) then
      View(BaseRoot(f)); Print("^",PowerOverBaseRoot(f)); return;
    fi;
    if IsOne(Modulus(f)) then Display(f:NoLineFeed); return; fi;
    cyclenotation := ValueOption("CycleNotation");
    if     IsRcwaMappingOfZ(f) and cyclenotation <> false
       and ( HasIsBijective(f) or cyclenotation = true ) and IsBijective(f)
       and ( cyclenotation = true or Length(Set(Coefficients(f))) <= 10 )
       and ( cyclenotation = true or HasIsTame(f) or IsIntegral(f) )
       and IsSignPreserving(f) and IsTame(f)
    then
      cycles := Filtered(Cycles(f,RespectedPartition(f)),
                         cycle->Length(cycle)>1);
      for i in [1..Length(cycles)] do
        Print("( ");
        for j in [1..Length(cycles[i])] do
          Print(ViewString(cycles[i][j]));
          if j < Length(cycles[i]) then Print(", "); fi;
        od;
        Print(" )");
        if i < Length(cycles) then Print(" "); fi;
      od;
    else
      Print("<");
      if   HasIsTame(f) and not (HasOrder(f) and IsInt(Order(f)))
      then if IsTame(f) then Print("tame "); else Print("wild "); fi; fi;
      if   HasIsBijective(f) and IsBijective(f)
      then Print("rcwa permutation");
      elif HasIsInjective(f) and IsInjective(f)
      then Print("injective rcwa mapping");
      elif HasIsSurjective(f) and IsSurjective(f)
      then Print("surjective rcwa mapping");
      else Print("rcwa mapping");
      fi;
      Print(" of ",RingToString(Source(f)));
      Print(" with modulus ",ModulusAsFormattedString(Modulus(f)));
      if IsRcwaMappingSparseRep(f) then
        Print(" and ",Length(f!.coeffs)," affine parts");
      fi;
      if   HasOrder(f) and not (HasIsTame(f) and not IsTame(f))
      then Print(", of order ",Order(f)); fi;
      Print(">");
    fi;
  end );

#############################################################################
##
#M  ViewObj( <elm> ) . . . . . . . for elements of group rings of rcwa groups
##
InstallMethod( ViewObj,
               "for elements of group rings of rcwa groups (RCWA)",
               ReturnTrue, [ IsElementOfFreeMagmaRing ], 100,

  function ( elm )

    local  l, grpelms, coeffs, supplng, g, i;

    if not IsRcwaMapping(CoefficientsAndMagmaElements(One(elm))[1]) then
      TryNextMethod();
    fi;
    l       := CoefficientsAndMagmaElements(elm);
    grpelms := l{[1,3..Length(l)-1]};
    coeffs  := l{[2,4..Length(l)]};
    supplng := Length(grpelms);
    if not ForAll(grpelms,IsRcwaMapping) then TryNextMethod(); fi;
    if supplng = 0 then Print("0"); return; fi;
    for i in [1..supplng] do
      if coeffs[i] < 0 then
        if i > 1 then Print(" - "); else Print("-"); fi;
      else
        if i > 1 then Print(" + "); fi;
      fi;
      if AbsInt(coeffs[i]) > 1 then Print(AbsInt(coeffs[i]),"*"); fi;
      ViewObj(grpelms[i]);
      if i < supplng then Print("\n"); fi;
    od;
  end );

#############################################################################
##
#M  Display( <f> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
##  Displays the rcwa mapping <f> in nice human-readable form.
##
InstallMethod( Display,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 10,

  function ( f )

    local  StringAffineMapping, StringAffineMappingOfZ, 
           StringAffineMappingOfZxZ, StringAffineMappingOfZ_pi,
           StringAffineMappingOfGFqx,

           R, F, F_el, F_elints, m, c, src, img, res, idcoeffs, inds,
           P, Pcl, D, affs, affstrings, maxafflng, lines, line, maxlinelng,
           cycles, cl, str, ustr, ringname, varname, maxsrclng, maximglng,
           looppos, prefix, col, i, j;

    StringAffineMappingOfZ := function ( t )

      local  append, str, a, b, c, n;

      append := function ( arg )
        str := CallFuncList(Concatenation,
                            Concatenation([str],List(arg,String)));
      end;

      a := t[1]; b := t[2]; c := t[3];
      str := ""; n := varname;

      if c > 1 and Number([a,b],n->n<>0) > 1 then append("("); fi;
      if a <> 0 then
        if a = -1 then append("-"); elif a <> 1 then append(a); fi;
        append(n);
        if b > 0 then
          if m = 1 then append(" + "); else append("+"); fi;
        fi;
      fi;
      if a = 0 or b <> 0 then
        if a = 0 or b > 0 then append(b); else
          if m = 1 then append(" - ",-b);
                   else append(b); fi;
        fi;
      fi;
      if c > 1 and Number([a,b],n->n<>0) > 1 then append(")"); fi;
      if c > 1 then append("/",c); fi;

      return str;
    end;

    StringAffineMappingOfZxZ := function ( t )

      local  Stringaff, append, str,
             a, b, c, d, e, f, g, d1, d2, g1, g2, m, n;

      Stringaff := function ( a, b, c, d )
        if d > 1 and Number([a,b,c],n->n<>0) > 1 then append("("); fi;
        if a <> 0 then
          if a = -1 then append("-"); elif a <> 1 then append(a); fi;
          append(m);
          if b > 0 or (b = 0 and c > 0) then append("+"); fi;
        fi;
        if b <> 0 then
          if b = -1 then append("-"); elif b <> 1 then append(b); fi;
          append(n);
          if c > 0 then append("+"); fi;
        fi;
        if (a = 0 and b = 0) or c <> 0 then append(c); fi;
        if d > 1 and Number([a,b,c],n->n<>0) > 1 then append(")"); fi;
        if d > 1 then append("/",d); fi;
      end;

      append := function ( arg )
        str := CallFuncList(Concatenation,
                            Concatenation([str],List(arg,String)));
      end;

      str := "";
      m := varname{[2]}; n := varname{[4]};
      a := t[1][1][1]; b := t[1][1][2];
      c := t[1][2][1]; d := t[1][2][2];
      e := t[2][1];    f := t[2][2];
      g := t[3];
      d1 := Gcd(a,c,e,g); d2 := Gcd(b,d,f,g);
      a := a/d1; c := c/d1; e := e/d1; g1 := g/d1;
      b := b/d2; d := d/d2; f := f/d2; g2 := g/d2;
      append("(");
      Stringaff(a,c,e,g1); append(","); Stringaff(b,d,f,g2);
      append(")");

      return str;
    end;

    StringAffineMappingOfZ_pi := function ( t )

      local  append, str, a, b, c, n;

      append := function ( arg )
        str := CallFuncList(Concatenation,
                            Concatenation([str],List(arg,String)));
      end;

      a := t[1]; b := t[2]; c := t[3];
      str := ""; n := varname;

      if   c = 1
      then if   a = 0
           then append(b);
           else if   AbsInt(a) <> 1 then append(a," ");
                elif a = -1         then append("-");
                fi;
                append(n);
                if   b > 0 then append(" + ", b);
                elif b < 0 then append(" - ",-b);
                fi;
           fi;
      elif b = 0 then if   AbsInt(a) <> 1 then append(a," ");
                      elif a = -1         then append("-");
                      fi;
                      append(n," / ",c);
      else append("(");
           if   AbsInt(a) <> 1 then append(a," ");
           elif a = -1         then append("-");
           fi;
           append(n);
           if   b > 0 then append(" + ", b);
           elif b < 0 then append(" - ",-b);
           fi;
           append(") / ",c);
      fi;

      return str;
    end;

    StringAffineMappingOfGFqx := function ( t )

      local  append, factorstr, str, a, b, c, P, one, zero, x;

      append := function ( arg )
        str := CallFuncList(Concatenation,
                            Concatenation([str],List(arg,String)));
      end;

      factorstr := function ( p )
        if   Length(CoefficientsOfLaurentPolynomial(p)[1]) <= 1
        then return String(p);
        else return Concatenation("(",String(p),")"); fi;
      end;

      a := t[1]; b := t[2]; c := t[3];
      str := ""; P := varname;

      one := One(a); zero := Zero(a);
      x := IndeterminateOfLaurentPolynomial(a);
 
      if   c = one
      then if   a = zero
           then append(b);
           else if   not a in [-one,one] then append(factorstr(a),"*",P);
                elif a = one then append(P); else append("-",P); fi;
                if b <> zero then append(" + ",b); fi;
           fi;
      elif b = zero then if   not a in [-one,one]
                         then append(factorstr(a),"*",P);
                         elif a = one then append(P);
                         else append("-",P); fi;
                         append("/",factorstr(c));
      else append("(");
           if   not a in [-one,one]
           then append(factorstr(a),"*",P," + ",b,")/",factorstr(c));
           elif a <> one and a = -one
           then append("-",P," + ",b,")/",factorstr(c));
           else append(P," + ",b,")/",factorstr(c));
           fi;
      fi;

      return str;
    end;

    R := Source(f);

    if   ValueOption("xdvi") = true and IsIntegers(R)
    then LaTeXAndXDVI(f); return; fi;

    # If option "AsTable" is set, use old-style format:
    if   ValueOption("AsTable") = true or ValueOption("table") = true
    then TryNextMethod(); fi;

    if   IsRcwaMappingOfZ(f)
    then StringAffineMapping := StringAffineMappingOfZ;
    elif IsRcwaMappingOfZxZ(f)
    then StringAffineMapping := StringAffineMappingOfZxZ;
    elif IsRcwaMappingOfZ_pi(f)
    then StringAffineMapping := StringAffineMappingOfZ_pi;
    elif IsRcwaMappingOfGFqx(f)
    then StringAffineMapping := StringAffineMappingOfGFqx; fi;

    m := Modulus(f); c := Coefficients(f); res := AllResidues(R,m);

    prefix := false; ringname := RingToString(Source(f));

    if   IsRcwaMappingOfGFqx(f) then varname := "P";
    elif IsRcwaMappingOfZxZ(f)  then
      varname := First(List(["varnames","VarNames"],ValueOption),
                       names->names<>fail);
      if varname = fail then varname := "mn"; fi;
      if Length(varname) = 2 then
        varname := Concatenation("(",varname{[1]},",",varname{[2]},")");
      fi;
    else varname := "n"; fi;

    if   IsOne(f)  then Print("Identity rcwa mapping of ",ringname);
    elif IsZero(f) then Print("Zero rcwa mapping of ",ringname);
    elif IsOne(m) and IsRcwaMappingStandardRep(f) and IsZero(c[1][1])
    then Print("Constant rcwa mapping of ",ringname," with value ",c[1][2]);
    elif IsOne(m) and IsRcwaMappingSparseRep(f) and IsZero(c[1][3])
    then Print("Constant rcwa mapping of ",ringname," with value ",c[1][4]);
    else
      if not IsOne(m) then Print("\n"); fi;

      if HasIsTame(f) and not (HasOrder(f) and IsInt(Order(f))) then
        if IsTame(f) then Print("Tame "); else Print("Wild "); fi;
        prefix := true;
      fi;
      if   HasIsBijective(f) and IsBijective(f)
      then if prefix then Print("rcwa permutation");
                     else Print("Rcwa permutation"); fi;
           prefix := true;
      elif HasIsInjective(f) and IsInjective(f)
      then if prefix then Print("injective rcwa mapping");
                     else Print("Injective rcwa mapping"); fi;
           prefix := true;
      elif HasIsSurjective(f) and IsSurjective(f)
      then if prefix then Print("surjective rcwa mapping");
                     else Print("Surjective rcwa mapping"); fi;
           prefix := true;
      fi;
      if not prefix then Print("Rcwa mapping"); fi;
      Print(" of ",ringname);

      if IsOne(m) then

        if   IsRcwaMappingStandardRep(f) then
          Print(": ",varname," -> ",StringAffineMapping(c[1]));
        elif IsRcwaMappingSparseRep(f) then
          Print(": ",varname," -> ",StringAffineMapping(c[1]{[3..5]}));
        fi;

      else

        Print(" with modulus ",ModulusAsFormattedString(m));
        if IsRcwaMappingSparseRep(f) then
          Print(" and ",Length(c)," affine parts");
        fi;
        if   HasOrder(f) and not (HasIsTame(f) and not IsTame(f))
        then Print(", of order ",Order(f)); fi;
        Print("\n\n");

        if   IsRcwaMappingOfZ(f) and HasIsBijective(f) and IsBijective(f)
          and (HasIsTame(f) and IsTame(f) or IsIntegral(f))
          and IsSignPreserving(f) and ValueOption("CycleNotation") <> false
        then
          cycles := Filtered(Cycles(f,RespectedPartition(f)),
                             cycle->Length(cycle)>1);
          maxlinelng := SizeScreen()[1]; col := 1;
          for i in [1..Length(cycles)] do
            Print("( "); col := col + 2;
            for j in [1..Length(cycles[i])] do
              str := ViewString(cycles[i][j]);
              Print(str); col := col + Length(str);
              if j < Length(cycles[i]) then
                Print(", "); col := col + 2;
                if col + Length(str) + 8 >= maxlinelng then
                  Print("\n  "); col := 3;
                fi;
              fi;
            od;
            Print(" )"); col := col + 2;
            if i < Length(cycles) then
              if   col + 20 >= maxlinelng
              then Print("\n"); col := 1;
              else Print(" "); col := col + 1; fi;
            else Print("\n\n");
            fi;
          od;
          return; # done.
        fi;

        if IsRcwaMappingOfZ(f) and ValueOption("AsClassMapping") = true then
          if   not IsRcwaMappingInSparseRep(f)
          then c := Coefficients(SparseRep(f)); fi;
          src := [];
          for i in [1..Length(c)] do
            Add(src,ResidueClass(c[i][1],c[i][2]));
          od;
          img := List(src,cl->cl^f);
          looppos := Filtered([1..Length(c)],i->img[i]<>src[i]
                              and Intersection(src[i],img[i])<>[]);
          src := List(src,ViewString);
          img := List(img,ViewString);
          maxsrclng := Maximum(List(src,Length));
          maximglng := Maximum(List(img,Length));
          for i in [1..Length(src)] do
            Print("  ",String(src[i],maxsrclng)," -> ",img[i]);
            if i in looppos then
              Print(String("",maximglng-Length(img[i]))," loop");
            fi;
            if c[i]{[3..5]} = [1,0,1] then
              Print(String("",maximglng-Length(img[i]))," id");
            fi;
            Print("\n");
          od;
          if ValueOption("NoLineFeed") <> true then Print("\n"); fi;
          return; # done.
        fi;

        P := ShallowCopy(LargestSourcesOfAffineMappings(f));
        D := List(P,src->[1/Density(src),src]);
        #i := First([1..Length(P)],j->IsOne(RestrictedMapping(f,P[j])));
        if   IsRing(R) then idcoeffs := [1,0,1] * One(R);
        elif IsZxZ(R)  then idcoeffs := [[[1,0],[0,1]],[0,0],1]; fi;
        if IsRcwaMappingStandardRep(f) then 
          i := First([1..Length(P)],
                     j -> c[First([1..Length(res)],k->res[k] in P[j])]
                        = idcoeffs);
        elif IsRcwaMappingOfZInSparseRep(f) then
          i := First([1..Length(P)],
                     j -> c[PositionProperty(c,d->d[1] in P[j])]{[3..5]}
                        = idcoeffs);
        fi;
        if i <> fail then D[i][1] := infinity; fi; # constant mappings -> end

        SortParallel(D,P);

        if   IsRcwaMappingStandardRep(f) then 
          affs := List(P,preimg->c[First([1..Length(res)],
                                         i->res[i] in preimg)]);
        elif IsRcwaMappingSparseRep(f) then
          affs := List(P,preimg->First(c,d->d[1] in preimg){[3..5]});
        fi;

        Pcl  := List(P,AsUnionOfFewClasses);

        affstrings := List(affs,StringAffineMapping);

        if IsRcwaMappingOfGFqx(f) and IsPrimeField(LeftActingDomain(R)) then
          F        := LeftActingDomain(R);
          F_el     := List(AsList(F),String);
          F_elints := List(List(AsList(F),Int),String);
          for i in [1..Length(affstrings)] do
            for j in [1..Length(F_el)] do
              affstrings[i] := ReplacedString(affstrings[i],
                                              F_el[j],F_elints[j]);
            od;
          od;
        fi;

        maxafflng  := Maximum(List(affstrings,Length));

        maxlinelng := SizeScreen()[1] - Length(varname) - 11;
        lines      := [String("/",Length(varname)+8)];

        for i in [1..Length(affs)] do
          line := String(affstrings[i],-maxafflng);
          if i < Length(affs) or Length(Pcl[i]) <= 2
            or (IsRcwaMappingOfZOrZ_pi(f) and Length(Pcl[i]) <= 4)
          then
            Append(line," if ");
            Append(line,varname);
            Append(line," in ");
            str := DisplayString(P[i]);
            if Length(line) + Length(str) <= maxlinelng then
              Append(line,str);
            else
              for j in [1..Length(Pcl[i])] do
                str := ViewString(Pcl[i][j]);
                if   j = Length(Pcl[i])
                then ustr := ""; else ustr := " U "; fi;
                if Length(line) + Length(str) + Length(ustr) > maxlinelng
                  and j > 1
                then
                  Add(lines,line);
                  line := String(" ",maxafflng+Length(" if ")+Length(varname)
                                              +Length(" in "));
                fi;
                Append(line,str);
                Append(line,ustr);
              od;
            fi;
          else
            Append(line," otherwise");
          fi;
          Add(lines,line);
        od;
        if   Length(lines) mod 2 = 1
        then Add(lines,String("|",Length(varname)+8)); fi;
        Add(lines,String("\\",Length(varname)+8));

        for i in [2..Length(lines)-1] do
          if i = (Length(lines)+1)/2 then
            lines[i] := Concatenation(" ",varname," |-> <  ",lines[i]);
          elif not '|' in lines[i] then
            lines[i] := Concatenation(String("|",Length(varname)+8)," ",
                                      lines[i]);
          fi;
        od;

        if IsRcwaMappingOfGFqx(f) and IsPrimeField(LeftActingDomain(R)) then
          for i in [1..Length(lines)] do
            for j in [1..Length(F_el)] do
              lines[i] := ReplacedString(lines[i],F_el[j],F_elints[j]);
            od;
          od;
        fi;

        for i in [1..Length(lines)] do
          Print(lines[i],"\n");
        od;

      fi;

    fi;

    if ValueOption("NoLineFeed") <> true then Print("\n"); fi;
  end );

#############################################################################
##
#M  Display( <f> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
##  Displays the rcwa mapping <f> as a table, in the "old-style" format used
##  by RCWA since its first release in 2005.
##  
InstallMethod( Display,
               "for rcwa mappings (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )

    local  IdChars, DisplayAffineMappingOfZ, DisplayAffineMappingOfZxZ,
           DisplayAffineMappingOfZ_pi, DisplayAffineMappingOfGFqx,
           R, m, c, r, poses, pos, i, scr, l1, l2, l3,
           str, ringname, mapname, varname, imageexpr,
           mstr, mcharstop, maxreschars, flushlng, prefix;

    IdChars := function ( n, ch )
      return Concatenation( ListWithIdenticalEntries( n, ch ) );
    end;

    DisplayAffineMappingOfZ := function ( t )

      local  a, b, c;

      a := t[1]; b := t[2]; c := t[3];
      if   c = 1
      then if   a = 0
           then Print(b);
           else if   AbsInt(a) <> 1 then Print(a);
                elif a = -1         then Print("-");
                fi;
                Print("n");
                if   b > 0 then Print(" + ", b);
                elif b < 0 then Print(" - ",-b);
                fi;
           fi;
      elif b = 0 then if   AbsInt(a) <> 1 then Print(a);
                      elif a = -1         then Print("-");
                      fi;
                      Print("n/",c);
      else Print("(");
           if   AbsInt(a) <> 1 then Print(a);
           elif a = -1         then Print("-");
           fi;
           Print("n");
           if   b > 0 then Print(" + ", b);
           elif b < 0 then Print(" - ",-b);
           fi;
           Print(")/",c);
      fi;
    end;

    DisplayAffineMappingOfZxZ := function ( t )

      local  Print_vxa, PrintAff,
             a, b, c, d, e, f, g, d1, d2, g1, g2, m, n;

      Print_vxa := function ( )
        if   IsOne( a) then Print("v");
        elif IsOne(-a) then Print("-v");
        else Print("v * ",BlankFreeString(a)); fi;
      end;

      PrintAff := function ( a, b, c, d )
        if d > 1 and Number([a,b,c],n->n<>0) > 1 then Print("("); fi;
        if a <> 0 then
          if a = -1 then Print("-"); elif a <> 1 then Print(a); fi;
          Print(m);
          if b > 0 or (b = 0 and c > 0) then Print("+"); fi;
        fi;
        if b <> 0 then
          if b = -1 then Print("-"); elif b <> 1 then Print(b); fi;
          Print(n);
          if c > 0 then Print("+"); fi;
        fi;
        if c <> 0 then Print(c); fi;
        if d > 1 and Number([a,b,c],n->n<>0) > 1 then Print(")"); fi;
        if d > 1 then Print("/",d); fi;
      end;

      if   varname = "v" then
        a := t[1]; b := t[2]; c := t[3];
        if   c = 1
        then if   IsZero(a)
             then Print(BlankFreeString(b));
             else Print_vxa();
                  if   not IsZero(b)
                  then Print(" + ",BlankFreeString(b)); fi;
             fi;
        elif IsZero(b) then Print_vxa(); Print("/",c);
        else Print("(");
             if   IsZero(a)
             then Print(BlankFreeString(b));
             else Print_vxa(); Print(" + ",BlankFreeString(b));
             fi;
             Print(")/",c);
        fi;
      elif Length(varname) = 5 then
        m := varname{[2]}; n := varname{[4]};
        a := t[1][1][1]; b := t[1][1][2];
        c := t[1][2][1]; d := t[1][2][2];
        e := t[2][1];    f := t[2][2];
        g := t[3];
        d1 := Gcd(a,c,e,g); d2 := Gcd(b,d,f,g);
        a := a/d1; c := c/d1; e := e/d1; g1 := g/d1;
        b := b/d2; d := d/d2; f := f/d2; g2 := g/d2;
        Print("[");
        PrintAff(a,c,e,g1); Print(","); PrintAff(b,d,f,g2);
        Print("]");
      else Print("<unknown output format>"); fi;
    end;

    DisplayAffineMappingOfZ_pi := function ( t )

      local  a, b, c;

      a := t[1]; b := t[2]; c := t[3];
      if   c = 1
      then if   a = 0
           then Print(b);
           else if   AbsInt(a) <> 1 then Print(a," ");
                elif a = -1         then Print("-");
                fi;
                Print("n");
                if   b > 0 then Print(" + ", b);
                elif b < 0 then Print(" - ",-b);
                fi;
           fi;
      elif b = 0 then if   AbsInt(a) <> 1 then Print(a," ");
                      elif a = -1         then Print("-");
                      fi;
                      Print("n / ",c);
      else Print("(");
           if   AbsInt(a) <> 1 then Print(a," ");
           elif a = -1         then Print("-");
           fi;
           Print("n");
           if   b > 0 then Print(" + ", b);
           elif b < 0 then Print(" - ",-b);
           fi;
           Print(") / ",c);
      fi;
    end;

    DisplayAffineMappingOfGFqx := function ( t, maxlng )

      local  append, factorstr, str, a, b, c, one, zero, x;

      append := function ( arg )
        str := CallFuncList(Concatenation,
                            Concatenation([str],List(arg,String)));
      end;

      factorstr := function ( p )
        if   Length(CoefficientsOfLaurentPolynomial(p)[1]) <= 1
        then return String(p);
        else return Concatenation("(",String(p),")"); fi;
      end;

      a := t[1]; b := t[2]; c := t[3];
      one := One(a); zero := Zero(a);
      x := IndeterminateOfLaurentPolynomial(a);
      str := "";
      if   c = one
      then if   a = zero
           then append(b);
           else if   not a in [-one,one] then append(factorstr(a),"*P");
                elif a = one then append("P"); else append("-P"); fi;
                if b <> zero then append(" + ",b); fi;
           fi;
      elif b = zero then if   not a in [-one,one]
                         then append(factorstr(a),"*P");
                         elif a = one then append("P");
                         else append("-P"); fi;
                         append("/",factorstr(c));
      else append("(");
           if   not a in [-one,one]
           then append(factorstr(a),"*P + ",b,")/",factorstr(c));
           elif a <> one and a = -one
           then append("-P + ",b,")/",factorstr(c));
           else append("P + ",b,")/",factorstr(c));
           fi;
      fi;
      if Length(str) > maxlng then str := "< ... >"; fi;
      Print(str);
    end;

    if   ValueOption("AsTable") <> true and ValueOption("table") <> true
    then TryNextMethod(); fi;

    R := Source(f);
    if   ValueOption("xdvi") = true and IsIntegers(R)
    then LaTeXAndXDVI(f); return; fi;

    m := Modulus(f); c := Coefficients(f); r := AllResidues(R,m);
    if HasName(f) and ValueOption("PrintName") <> fail then
      mapname := Name(f);
      if   Position(mapname,'^') <> fail
      then mapname := Concatenation("(",mapname,")"); fi;
    else mapname := "Image of "; fi;
    prefix := false; ringname := RingToString(Source(f));
    if   IsRcwaMappingOfGFqx(f) then varname := "P";
    elif IsRcwaMappingOfZxZ(f)  then
      varname := First(List(["varnames","VarNames"],ValueOption),
                       names->names<>fail);
      if varname = fail then varname := "mn"; fi;
      if Length(varname) = 2 then
        varname := Concatenation("[",varname{[1]},",",varname{[2]},"]");
      fi;
    else varname := "n"; fi;
    maxreschars := Maximum(List(List(r,BlankFreeString),Length));
    if   IsOne(f)
    then Print("Identity rcwa mapping of ",ringname);
    elif IsZero(f)
    then Print("Zero rcwa mapping of ",ringname);
    elif IsOne(m) and IsZero(c[1][1])
    then Print("Constant rcwa mapping of ",ringname,
               " with value ",c[1][2]);
    else if not IsOne(m) then Print("\n"); fi;
         if HasIsTame(f) and not (HasOrder(f) and IsInt(Order(f))) then
           if IsTame(f) then Print("Tame "); else Print("Wild "); fi;
           prefix := true;
         fi;
         if   HasIsBijective(f) and IsBijective(f)
         then if prefix then Print("rcwa permutation");
                        else Print("Rcwa permutation"); fi;
              prefix := true;
         elif HasIsInjective(f) and IsInjective(f)
         then if prefix then Print("injective rcwa mapping");
                        else Print("Injective rcwa mapping"); fi;
              prefix := true;
         elif HasIsSurjective(f) and IsSurjective(f)
         then if prefix then Print("surjective rcwa mapping");
                        else Print("Surjective rcwa mapping"); fi;
              prefix := true;
         fi;
         if not prefix then Print("Rcwa mapping"); fi;
         Print(" of ",ringname);
         if IsOne(m) then
           Print(": ",varname," -> ");
           if   IsRcwaMappingOfZ(f)
           then DisplayAffineMappingOfZ(c[1]);
           elif IsRcwaMappingOfZxZ(f)
           then DisplayAffineMappingOfZxZ(c[1]);
           elif IsRcwaMappingOfZ_pi(f)
           then DisplayAffineMappingOfZ_pi(c[1]);
           else DisplayAffineMappingOfGFqx(c[1],SizeScreen()[1]-48); fi;
         else
           Print(" with modulus ",ModulusAsFormattedString(m));
           if   HasOrder(f) and not (HasIsTame(f) and not IsTame(f))
           then Print(", of order ",Order(f)); fi;
           Print("\n\n");
           scr := SizeScreen()[1] - 2;
           if   IsRcwaMappingOfZOrZ_pi(f) then l1 := Int(scr/2);
           elif IsRcwaMappingOfZxZ(f)     then l1 := Int(2*scr/5);
           else                                l1 := Int(scr/3); fi;
           mstr := ModulusAsFormattedString(m);
           if l1 - Length(mstr) - 6 <= 0 then mstr := "<modulus>"; fi;
           mcharstop := Length(mstr) + Length(varname) - 1;
           l2 := Int((l1 - mcharstop - 6)/2);
           l3 := Int((scr - l1 - Length(mapname) - 3)/2);
           if   l3 < 3
           then mapname := "Image of "; l3 := Int((scr-l1-12)/2); fi;
           if Length(varname) = 5 then l3 := l3 - 2; fi;
           if   mapname = "Image of "
           then imageexpr := Concatenation(mapname,varname);
           else imageexpr := Concatenation(varname,"^",mapname); fi;
           flushlng := l1 - maxreschars - 1;
           Print(IdChars(l2," "),varname," mod ",mstr,
                 IdChars(l1-l2-mcharstop-6," "),"|",IdChars(l3," "),
                 imageexpr,"\n",IdChars(l1,"-"),"+",IdChars(scr-l1-1,"-"));
           poses := AsSortedList(List(Set(c),t->Positions(c,t)));
           for pos in poses do
             str := " ";
             for i in pos do
               if IsRcwaMappingOfZOrZ_pi(f) then
                 Append(str,String(r[i],maxreschars+1));
               else
                 Append(str,String(BlankFreeString(r[i]),-(maxreschars+1)));
               fi;
               if Length(str) >= flushlng then
                 if   Length(str) < l1
                 then Print("\n",String(str, -l1),"| ");
                 else Print("\n",String(" < ... > ",-l1),"| "); fi;
                 str := " ";
               fi;
             od;
             if   str <> " " 
             then Print("\n",String(str, -l1),"| "); fi;
             if   IsRcwaMappingOfZ(f)
             then DisplayAffineMappingOfZ(c[pos[1]]);
             elif IsRcwaMappingOfZxZ(f)
             then DisplayAffineMappingOfZxZ(c[pos[1]]);
             elif IsRcwaMappingOfZ_pi(f)
             then DisplayAffineMappingOfZ_pi(c[pos[1]]);
             else DisplayAffineMappingOfGFqx(c[pos[1]],scr-l1-4); fi;
           od;
           Print("\n");
         fi;
    fi;
    if ValueOption("NoLineFeed") <> true then Print("\n"); fi;
  end );

#############################################################################
##
#M  LaTeXStringRcwaMapping( <f> ) . . . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( LaTeXStringRcwaMapping,
               "for rcwa mappings of Z in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZInStandardRep ], 0,

  function ( f )

    local  LaTeXAffineMappingOfZ, append, indent, varname, german,
           gens, c, m, res, P, str, affs, affstrings, maxafflng, i, j;

    append := function ( arg )
      str := CallFuncList(Concatenation,
                          Concatenation([str],List(arg,String)));
    end;

    LaTeXAffineMappingOfZ := function ( t )

      local  append, str, a, b, c, n;

      append := function ( arg )
        str := CallFuncList(Concatenation,
                            Concatenation([str],List(arg,String)));
      end;

      a := t[1]; b := t[2]; c := t[3];
      str := ""; n := varname;

      if c > 1 and Number([a,b],n->n<>0) > 1 then append("("); fi;
      if a <> 0 then
        if a = -1 then append("-"); elif a <> 1 then append(a); fi;
        append(n);
        if b > 0 then append("+"); fi;
      fi;
      if a = 0 or b <> 0 then append(b); fi;
      if c > 1 and Number([a,b],n->n<>0) > 1 then append(")"); fi;
      if c > 1 then append("/",c); fi;

      return str;
    end;

    if HasLaTeXString(f) then return LaTeXString(f); fi;

    indent := ValueOption("Indentation");
    if not IsPosInt(indent)
    then indent := ""; else indent := String(" ",indent); fi;
    str := indent;

    if ValueOption("Factorization") = true and IsBijective(f) then
      gens := List(FactorizationIntoCSCRCT(f),LaTeXString);
      append("      &");
      for i in [1..Length(gens)] do
        append(gens[i]);
        if i < Length(gens) then
          if i mod 5 = 0 then append(" \\\\\n"); fi;
          if i mod 5 in [2,4] then append("\n"); fi;
          append(" \\cdot ");
          if i mod 5 = 0 then append("&"); fi;
        else append("\n"); fi;
      od;
      return str;
    fi;

    german :=   ValueOption("German") = true
             or ValueOption("german") = true;
    varname := First(List(["varname","VarName"],ValueOption),
                     name->name<>fail);
    if varname = fail then varname := "n"; fi;

    c := Coefficients(f); m := Length(c);
    if m = 1 then
      return Concatenation("n \\ \\mapsto \\ ",LaTeXAffineMappingOfZ(c[1]));
    fi;
    res := AllResidues(Integers,m);

    append("n \\ \\mapsto \\\n",indent,"\\begin{cases}\n");

    P := ShallowCopy(LargestSourcesOfAffineMappings(f));
    Sort(P,function(Pi,Pj) return Density(Pi)>Density(Pj); end);

    affs := List(P,preimg->c[First([1..Length(res)],i->res[i] in preimg)]);
    P    := List(P,AsUnionOfFewClasses);

    affstrings := List( affs, LaTeXAffineMappingOfZ );
    maxafflng  := Maximum( List( affstrings, Length ) );

    for i in [1..Length(P)] do
      append(indent,"  ",affstrings[i],
             String("",maxafflng-Length(affstrings[i])));
      if german then append(" & \\text{falls}");
                else append(" & \\text{if}"); fi;
      append(" \\ ",varname," \\in ");
      for j in [1..Length(P[i])] do
        append(String(Residue(P[i][j])),"(",String(Modulus(P[i][j])),")");
        if j < Length(P[i]) then append(" \\cup "); fi;
      od;
      if i = Length(P) then append(".\n"); else append(", \\\\\n"); fi;
    od;

    append(indent,"\\end{cases}\n");
    return str;
  end );

#############################################################################
##
#M  LaTeXStringRcwaMapping( <f> ) . . . . . . . . .  for rcwa mappings of Z^2
##
InstallMethod( LaTeXStringRcwaMapping,
               "for rcwa mappings of Z^2 (RCWA)",
               true, [ IsRcwaMappingOfZxZ ], 0,

  function ( f )

    local  LaTeXAffineMappingOfZxZ, append, indent, varname, german,
           gens, c, m, res, P, str, affs, affstrings, maxafflng, i, j;

    append := function ( arg )
      str := CallFuncList(Concatenation,
                          Concatenation([str],List(arg,String)));
    end;

    LaTeXAffineMappingOfZxZ := function ( t )

      local  append, LaTeXaff, str,
             a, b, c, d, e, f, g, d1, d2, g1, g2, m, n;

      append := function ( arg )
        str := CallFuncList(Concatenation,
                            Concatenation([str],List(arg,String)));
      end;

      LaTeXaff := function ( a, b, c, d )
        if d > 1 and Number([a,b,c],n->n<>0) > 1 then append("("); fi;
        if a <> 0 then
          if a = -1 then append("-"); elif a <> 1 then append(a); fi;
          append(m);
          if b > 0 or (b = 0 and c > 0) then append("+"); fi;
        fi;
        if b <> 0 then
          if b = -1 then append("-"); elif b <> 1 then append(b); fi;
          append(n);
          if c > 0 then append("+"); fi;
        fi;
        if (a = 0 and b = 0) or c <> 0 then append(c); fi;
        if d > 1 and Number([a,b,c],n->n<>0) > 1 then append(")"); fi;
        if d > 1 then append("/",d); fi;
      end;

      str := "";
      m := varname{[1]}; n := varname{[2]};
      a := t[1][1][1]; b := t[1][1][2];
      c := t[1][2][1]; d := t[1][2][2];
      e := t[2][1];    f := t[2][2];
      g := t[3];
      d1 := Gcd(a,c,e,g); d2 := Gcd(b,d,f,g);
      a := a/d1; c := c/d1; e := e/d1; g1 := g/d1;
      b := b/d2; d := d/d2; f := f/d2; g2 := g/d2;
      append("(");
      LaTeXaff(a,c,e,g1); append(","); LaTeXaff(b,d,f,g2);
      append(")");
      return str;
    end;

    if HasLaTeXString(f) then return LaTeXString(f); fi;

    indent := ValueOption("Indentation");
    if not IsPosInt(indent)
    then indent := ""; else indent := String(" ",indent); fi;
    str := indent;

    if ValueOption("Factorization") = true and IsBijective(f) then
      gens := List(FactorizationIntoCSCRCT(f),LaTeXString);
      append("      &");
      for i in [1..Length(gens)] do
        append(gens[i]);
        if i < Length(gens) then
          if i mod 2 = 0 then append(" \\\\\n"); else append("\n"); fi;
          append(" \\cdot ");
          if i mod 2 = 0 then append("&"); fi;
        else append("\n"); fi;
      od;
      return str;
    fi;

    german :=   ValueOption("German") = true
             or ValueOption("german") = true;
    varname := First(List(["varnames","VarNames"],ValueOption),
                     names->names<>fail);
    if varname = fail then varname := "mn"; fi;

    c := Coefficients(f); m := Modulus(f);
    if IsOne(m) then
      return Concatenation("(",varname{[1]},",",varname{[2]},")",
                           "\\ \\mapsto \\ ",
                           LaTeXAffineMappingOfZxZ(c[1]));
    fi;
    res := AllResidues(Integers^2,m);

    append("(",varname{[1]},",",varname{[2]},")","\\ \\mapsto \\\n",
           indent,"\\begin{cases}\n");

    P := ShallowCopy(LargestSourcesOfAffineMappings(f));
    Sort(P,function(Pi,Pj) return Density(Pi)>Density(Pj); end);

    affs := List(P,preimg->c[First([1..Length(res)],i->res[i] in preimg)]);
    P    := List(P,AsUnionOfFewClasses);

    affstrings := List( affs, LaTeXAffineMappingOfZxZ );
    maxafflng  := Maximum( List( affstrings, Length ) );

    for i in [1..Length(P)] do
      append(indent,"  ",affstrings[i],
             String("",maxafflng-Length(affstrings[i])));
      if german then append(" & \\text{falls}");
                else append(" & \\text{if}"); fi;
      append(" \\ (",varname{[1]},",",varname{[2]},") \\in ");
      for j in [1..Length(P[i])] do
        append(ReplacedString(ViewString(P[i][j]),"Z","\\mathbb{Z}"));
        if j < Length(P[i]) then append(" \\cup "); fi;
      od;
      if i = Length(P) then append(".\n"); else append(", \\\\\n"); fi;
    od;

    append(indent,"\\end{cases}\n");
    return str;
  end );

#############################################################################
##
#M  LaTeXAndXDVI( <f> ) . . . . . . . . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( LaTeXAndXDVI,
               "for rcwa mappings of Z", true, [ IsRcwaMappingOfZ ], 0,

  function ( f )

    local  tmpdir, file, stream, str, latex, dvi, m, sizes, size,
           jectivity, cwop;

    tmpdir := DirectoryTemporary( );
    file   := Filename(tmpdir,"rcwamap.tex");
    stream := OutputTextFile(file,false);
    SetPrintFormattingStatus(stream,false);
    AppendTo(stream,"\\documentclass[fleqn]{article}\n",
                    "\\usepackage{amsmath}\n",
                    "\\usepackage{amssymb}\n\n",
                    "\\setlength{\\paperwidth}{84cm}\n",
                    "\\setlength{\\textwidth}{80cm}\n",
                    "\\setlength{\\paperheight}{59.5cm}\n",
                    "\\setlength{\\textheight}{57cm}\n\n", 
                    "\\begin{document}\n\n");
    sizes := ["Huge","huge","Large","large"];
    m := Modulus(f);
    if   ValueOption("Factorization") <> true
    then size := LogInt(Int(m/16)+1,2)+1;
    else size := Int(Length(FactorizationIntoCSCRCT(f))/50) + 1; fi;
    if size < 5 then AppendTo(stream,"\\begin{",sizes[size],"}\n\n"); fi;
    if   IsBijective(f)  then jectivity := " bijective";
    elif IsInjective(f)  then jectivity := "n injective, but not surjective";
    elif IsSurjective(f) then jectivity := " surjective, but not injective";
    else jectivity := " neither injective nor surjective"; fi;
    if   IsClassWiseOrderPreserving(f)
    then cwop := " class-wise order-preserving"; else cwop := ""; fi;
    AppendTo(stream,"\\noindent A",jectivity,cwop,
             " rcwa mapping of \\(\\mathbb{Z}\\) \\newline\nwith modulus ",
             String(Modulus(f)),", multiplier ",String(Multiplier(f)),
             " and divisor ",String(Divisor(f)),", given by\n");
    AppendTo(stream,"\\begin{align*}\n");
    str := LaTeXStringRcwaMapping(f:Indentation:=2);
    AppendTo(stream,str,"\\end{align*}");
    if HasIsTame(f) then
      if IsTame(f) then AppendTo(stream,"\nThis mapping is tame.");
                   else AppendTo(stream,"\nThis mapping is wild."); fi;
    fi;
    if HasOrder(f) then
      AppendTo(stream,"\nThe order of this mapping is \\(",
               IntOrInfinityToLaTeX(Order(f)),"\\).");
    fi;
    if HasIsTame(f) or HasOrder(f) then AppendTo(stream," \\newline"); fi;
    if IsBijective(f) then
      if IsClassWiseOrderPreserving(f) then
        AppendTo(stream,"\n\\noindent The determinant of this mapping is ",
                 String(Determinant(f)),", and its sign is ",
                 String(Sign(f)),".");
      else
        AppendTo(stream,"\n\\noindent The sign of this mapping is ",
                 String(Sign(f)),".");
      fi;
    fi;
    if size < 5 then AppendTo(stream,"\n\n\\end{",sizes[size],"}"); fi;
    AppendTo(stream,"\n\n\\end{document}\n");
    latex := Filename(DirectoriesSystemPrograms( ),"latex");
    Process(tmpdir,latex,InputTextNone( ),OutputTextNone( ),[file]);
    dvi := Filename(DirectoriesSystemPrograms( ),"xdvi");
    Process(tmpdir,dvi,InputTextNone( ),OutputTextNone( ), 
            ["-paper","a1r","rcwamap.dvi"]);
  end );

#############################################################################
##
#M  LaTeXAndXDVI( <f> ) . . . . . . . . . . . . . .  for rcwa mappings of ZxZ
##
InstallMethod( LaTeXAndXDVI,
               "for rcwa mappings of ZxZ", true, [ IsRcwaMappingOfZxZ ], 0,

  function ( f )

    local  tmpdir, file, stream, str, latex, dvi, jectivity, cwop;

    tmpdir := DirectoryTemporary( );
    file   := Filename(tmpdir,"rcwamap.tex");
    stream := OutputTextFile(file,false);
    SetPrintFormattingStatus(stream,false);
    AppendTo(stream,"\\documentclass[fleqn]{article}\n",
                    "\\usepackage{amsmath}\n",
                    "\\usepackage{amssymb}\n\n",
                    "\\setlength{\\paperwidth}{84cm}\n",
                    "\\setlength{\\textwidth}{80cm}\n",
                    "\\setlength{\\paperheight}{59.5cm}\n",
                    "\\setlength{\\textheight}{57cm}\n\n", 
                    "\\begin{document}\n\n");
    if   IsBijective(f)  then jectivity := " bijective";
    elif IsInjective(f)  then jectivity := "n injective, but not surjective";
    elif IsSurjective(f) then jectivity := " surjective, but not injective";
    else jectivity := " neither injective nor surjective"; fi;
    if   IsClassWiseOrderPreserving(f)
    then cwop := " class-wise order-preserving"; else cwop := ""; fi;
    AppendTo(stream,"\\noindent A",jectivity,cwop,
             " rcwa mapping of \\(\\mathbb{Z}^2\\) with modulus ",
             "\\(",ReplacedString(ModulusAsFormattedString(Modulus(f)),"Z",
                                                           "\\mathbb{Z}"),
             "\\), given by\n");
    AppendTo(stream,"\\begin{align*}\n");
    str := LaTeXStringRcwaMapping(f:Indentation:=2);
    AppendTo(stream,str,"\\end{align*}");
    if HasIsTame(f) then
      if IsTame(f) then AppendTo(stream,"\nThis mapping is tame.");
                   else AppendTo(stream,"\nThis mapping is wild."); fi;
    fi;
    if HasOrder(f) then
      AppendTo(stream,"\nThe order of this mapping is \\(",
               IntOrInfinityToLaTeX(Order(f)),"\\).");
    fi;
    if HasIsTame(f) or HasOrder(f) then AppendTo(stream," \\newline"); fi;
    AppendTo(stream,"\n\n\\end{document}\n");
    latex := Filename(DirectoriesSystemPrograms( ),"latex");
    Process(tmpdir,latex,InputTextNone( ),OutputTextNone( ),[file]);
    dvi := Filename(DirectoriesSystemPrograms( ),"xdvi");
    Process(tmpdir,dvi,InputTextNone( ),OutputTextNone( ), 
            ["-paper","a1r","rcwamap.dvi"]);
  end );

#############################################################################
##
#S  Comparing rcwa mappings. ////////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  \=( <f>, <g> ) . . . . . . . . . . . . . for rcwa mappings of Z or Z_(pi)
##
InstallMethod( \=,
               "for two rcwa mappings of Z or Z_(pi), standard rep. (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZOrZ_piInStandardRep,
                 IsRcwaMappingOfZOrZ_piInStandardRep ], 0,
               function ( f, g ) return f!.coeffs = g!.coeffs; end );
InstallMethod( \=,
               "for two rcwa mappings of Z or Z_(pi), sparse rep. (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZOrZ_piInSparseRep,
                 IsRcwaMappingOfZOrZ_piInSparseRep ], 0,
               function ( f, g ) return f!.coeffs = g!.coeffs; end );

#############################################################################
##
#M  \=( <f>, <g> ) . . . . . . . . . . . . . . . . . for rcwa mappings of Z^2
##
InstallMethod( \=,
               "for two rcwa mappings of Z^2 (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZxZInStandardRep,
                 IsRcwaMappingOfZxZInStandardRep ], 0,

  function ( f, g )
    return f!.modulus = g!.modulus and f!.coeffs = g!.coeffs;
  end );

#############################################################################
##
#M  \=( <f>, <g> ) . . . . . . . . . . . . . .  for rcwa mappings of GF(q)[x]
##
InstallMethod( \=,
               "for two rcwa mappings of GF(q)[x] (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfGFqxInStandardRep,
                 IsRcwaMappingOfGFqxInStandardRep ], 0,

  function ( f, g )
    return f!.modulus = g!.modulus and f!.coeffs = g!.coeffs;
  end );

#############################################################################
##
#M  \=( <f>, <g> ) . . . . . . .  for rcwa mappings, standard vs. sparse rep.
#M  \=( <f>, <g> ) . . . . . . .  for rcwa mappings, sparse vs. standard rep.
##
InstallMethod( \=,
               "for two rcwa mappings, standard vs. sparse rep. (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingInStandardRep, IsRcwaMappingInSparseRep ], 0,
               function ( f, g ) return SparseRepresentation(f) = g; end );
InstallMethod( \=,
               "for two rcwa mappings, sparse vs. standard rep. (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingInSparseRep, IsRcwaMappingInStandardRep ], 0,
               function ( f, g ) return f = SparseRepresentation(g); end );

#############################################################################
##
#M  \<( <f>, <g> ) . . . . . . . . . . . . for rcwa mappings in standard rep.
#M  \<( <f>, <g> ) . . . . . . . . . . . . . for rcwa mappings in sparse rep.
#M  \<( <f>, <g> ) . . . . . . .  for rcwa mappings: standard vs. sparse rep.
#M  \<( <f>, <g> ) . . . . . . .  for rcwa mappings: sparse vs. standard rep.
##
##  Total ordering of rcwa maps (for technical purposes, only).
##  More methods are needed as soon as further representations of
##  rcwa mappings are implemented.
##
InstallMethod( \<,
               "for rcwa mappings in standard rep. (RCWA)", IsIdenticalObj,
               [ IsRcwaMappingInStandardRep, IsRcwaMappingInStandardRep ], 0,

  function ( f, g )
    if   f!.modulus <> g!.modulus
    then return f!.modulus < g!.modulus;
    else return f!.coeffs  < g!.coeffs; fi;
  end );

InstallMethod( \<,
               "for rcwa mappings in sparse rep. (RCWA)", IsIdenticalObj,
               [ IsRcwaMappingInSparseRep, IsRcwaMappingInSparseRep ], 0,

  function ( f, g )

    local  r, m, cf, cg;

    if   f!.modulus <> g!.modulus
    then return f!.modulus < g!.modulus;
    elif f = g
    then return false; else
      m := f!.modulus; r := 0;
      while r < m do
        cf := First(f!.coeffs,c->c[1] = r mod c[2]){[3..5]};
        cg := First(g!.coeffs,c->c[1] = r mod c[2]){[3..5]};
        if cf <> cg then return cf < cg; fi;
        r := r + 1;
      od;
    fi;
  end );

InstallMethod( \<,
               "for rcwa mappings: standard vs. sparse rep. (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingInStandardRep, IsRcwaMappingInSparseRep ], 0,

  function ( f, g )

    local  r, m, cf, cg;

    if   f!.modulus <> g!.modulus
    then return f!.modulus < g!.modulus;
    elif f = g
    then return false; else
      m := f!.modulus; r := 0;
      while r < m do
        cf := f!.coeffs[r+1];
        cg := First(g!.coeffs,c->c[1] = r mod c[2]){[3..5]};
        if cf <> cg then return cf < cg; fi;
        r := r + 1;
      od;
    fi;
  end );

InstallMethod( \<,
               "for rcwa mappings: sparse vs. standard rep. (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingInSparseRep, IsRcwaMappingInStandardRep ], 0,

  function ( f, g )

    local  r, m, cf, cg;

    if   f!.modulus <> g!.modulus
    then return f!.modulus < g!.modulus;
    elif f = g
    then return false; else
      m := f!.modulus; r := 0;
      while r < m do
        cf := First(f!.coeffs,c->c[1] = r mod c[2]){[3..5]};
        cg := g!.coeffs[r+1];
        if cf <> cg then return cf < cg; fi;
        r := r + 1;
      od;
    fi;
  end );

#############################################################################
##
#S  On the zero- and the identity rcwa mapping. /////////////////////////////
##
#############################################################################

#############################################################################
##
#V  ZeroRcwaMappingOfZ . . . . . . . . . . . . . . . . zero rcwa mapping of Z
#V  ZeroRcwaMappingOfZxZ . . . . . . . . . . . . . . zero rcwa mapping of Z^2
##
InstallValue( ZeroRcwaMappingOfZ, RcwaMapping( [ [ 0, 0, 1 ] ] ) );
SetIsZero( ZeroRcwaMappingOfZ, true );
SetImagesSource( ZeroRcwaMappingOfZ, [ 0 ] );
InstallValue( ZeroRcwaMappingOfZxZ,
              RcwaMapping( Integers^2, [ [ 1, 0 ], [ 0, 1 ] ],
                           [ [ [ [ 0, 0 ], [ 0, 0 ] ], [ 0, 0 ], 1 ] ] ) );
SetIsZero( ZeroRcwaMappingOfZxZ, true );
SetImagesSource( ZeroRcwaMappingOfZ, [ 0, 0 ] );

#############################################################################
##
#M  Zero( <f> ) . . . . . . . . . . . for rcwa mappings of Z in standard rep.
#M  Zero( <f> ) . . . . . . . . . . . . for rcwa mappings of Z in sparse rep.
#M  Zero( <f> ) . . . . . . . . . . . . . . . . . .  for rcwa mappings of Z^2
##
##  Zero rcwa mapping of Z or Z^2, respectively.
##
InstallMethod( Zero, "for rcwa mappings of Z in standard rep. (RCWA)", true,
               [ IsRcwaMappingOfZInStandardRep ], 0,
               f -> ZeroRcwaMappingOfZ );
InstallMethod( Zero, "for rcwa mappings of Z in sparse rep. (RCWA)", true,
               [ IsRcwaMappingOfZInSparseRep ], 0,
               f -> SparseRep( ZeroRcwaMappingOfZ ) );
InstallMethod( Zero, "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZInStandardRep ], 0,
               f -> ZeroRcwaMappingOfZxZ );

#############################################################################
##
#M  Zero( <f> ) . . . . . . . . . . . . . . . . . for rcwa mappings of Z_(pi)
##
##  Zero rcwa mapping of Z_(pi).
##
InstallMethod( Zero, "for rcwa mappings of Z_(pi) (RCWA)", true,
               [ IsRcwaMappingOfZ_piInStandardRep ], 0,

  function ( f )

    local  zero;

    zero := RcwaMappingNC( NoninvertiblePrimes(Source(f)), [ [ 0, 0, 1 ] ] );
    SetIsZero( zero, true );
    SetImagesSource( zero, [ 0 ] );
    return zero;
  end );

#############################################################################
##
#M  Zero( <f> ) . . . . . . . . . . . . . . . . for rcwa mappings of GF(q)[x]
##
##  Zero rcwa mapping of GF(q)[x].
##
InstallMethod( Zero, "for rcwa mappings of GF(q)[x] (RCWA)", true,
               [ IsRcwaMappingOfGFqxInStandardRep ], 0,

  function ( f )

    local  zero;

    zero := RcwaMappingNC( Size(UnderlyingField(f)), One(Source(f)),
                           [ [ 0, 0, 1 ] ] * One(Source(f)) );
    SetIsZero( zero, true );
    SetImagesSource( zero, [ Zero(Source(f)) ] );
    return zero;
  end );

#############################################################################
##
#M  IsZero( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
##  <f> = zero rcwa mapping?
##
InstallMethod( IsZero, "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )
    if not IsRing( Source( f ) ) then TryNextMethod( ); fi;
    return f!.coeffs = [ [ 0, 0, 1 ] ] * One( Source( f ) );
  end );

InstallMethod( IsZero, "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               f -> f!.coeffs = [ [ 0, 1, 0, 0, 1 ] ] );

InstallMethod( IsZero, "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZInStandardRep ], 0,
               f -> f = ZeroRcwaMappingOfZxZ );

#############################################################################
##
#V  IdentityRcwaMappingOfZ . . . . . . . . . . . . identity rcwa mapping of Z
#V  IdentityRcwaMappingOfZxZ . . . . . . . . . . identity rcwa mapping of Z^2
##
InstallValue( IdentityRcwaMappingOfZ, RcwaMapping( [ [ 1, 0, 1 ] ] ) );
SetIsOne( IdentityRcwaMappingOfZ, true );
InstallValue( IdentityRcwaMappingOfZxZ,
              RcwaMapping( Integers^2, [ [ 1, 0 ], [ 0, 1 ] ],
                           [ [ [ [ 1, 0 ], [ 0, 1 ] ], [ 0, 0 ], 1 ] ] ) );
SetIsOne( IdentityRcwaMappingOfZxZ, true );

#############################################################################
##
#M  One( <f> ) . . . . . . . . . . .  for rcwa mappings of Z in standard rep.
#M  One( <f> ) . . . . . . . . . . . .  for rcwa mappings of Z in sparse rep.
#M  One( <f> ) . . . . . . . . . . . . . . . . . . . for rcwa mappings of Z^2
##
##  Identity rcwa mapping of Z or Z^2, respectively.
##
InstallMethod( One, "for rcwa mappings of Z in standard rep. (RCWA)", true,
               [ IsRcwaMappingOfZInStandardRep ], 0,
               f -> IdentityRcwaMappingOfZ );
InstallMethod( One, "for rcwa mappings of Z in sparse rep. (RCWA)", true,
               [ IsRcwaMappingOfZInSparseRep ], 0,
               f -> SparseRep( IdentityRcwaMappingOfZ ) );
InstallMethod( One, "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZInStandardRep ], 0,
               f -> IdentityRcwaMappingOfZxZ );

#############################################################################
##
#M  One( <f> ) . . . . . . . . . . . . . . . . .  for rcwa mappings of Z_(pi)
##
##  Identity rcwa mapping of Z_(pi).
##
InstallMethod( One, "for rcwa mappings of Z_(pi) (RCWA)", true,
               [ IsRcwaMappingOfZ_piInStandardRep ], 0,

  function ( f )

    local  one;

    one := RcwaMappingNC( NoninvertiblePrimes(Source(f)), [ [ 1, 0, 1 ] ] );
    SetIsOne( one, true ); return one;
  end );

#############################################################################
##
#M  One( <f> ) . . . . . . . . . . . . . . . .  for rcwa mappings of GF(q)[x]
##
##  Identity rcwa mapping of GF(q)[x].
##
InstallMethod( One, "for rcwa mappings of GF(q)[x] (RCWA)", true,
               [ IsRcwaMappingOfGFqxInStandardRep ], 0,

  function ( f )

    local  one;
 
    one := RcwaMappingNC( Size(UnderlyingField(f)), One(Source(f)),
                          [ [ 1, 0, 1 ] ] * One( Source( f ) ) );
    SetIsOne( one, true ); return one;
  end );

#############################################################################
## 
#M  IsOne( <f> ) . . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
## 
##  <f> = identity rcwa mapping?
##
InstallMethod( IsOne, "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )
    if not IsRing( Source( f ) ) then TryNextMethod( ); fi;
    return f!.coeffs = [ [ 1, 0, 1 ] ] * One( Source( f ) );
  end );

InstallMethod( IsOne, "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               f -> f!.coeffs = [ [ 0, 1, 1, 0, 1 ] ] );

InstallMethod( IsOne, "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZInStandardRep ], 0,
               f -> f = IdentityRcwaMappingOfZxZ );

#############################################################################
##
#M  ViewString( <zero> ) . . . . . . . . . . . . .  for the zero rcwa mapping
#M  ViewString( <one> )  . . . . . . . . . . .  for the identity rcwa mapping
##
InstallMethod( ViewString, "for the zero rcwa mapping (RCWA)", true,
               [ IsRcwaMapping and IsZero ], 0,
               f -> Concatenation("ZeroMapping( ",String(Source(f)),", ",
                                                  String(Source(f))," )") );

InstallMethod( ViewString, "for the identity rcwa mapping (RCWA)", true,
               [ IsRcwaMapping and IsOne ], 0,
               f -> Concatenation("IdentityMapping( ",
                                  String(Source(f))," )") );

#############################################################################
##
#S  Accessing the components of an rcwa mapping object. /////////////////////
##
#############################################################################

#############################################################################
##
#M  Modulus( <f> ) . . . . . . . for rcwa mappings in standard representation
#M  Modulus( <f> ) . . . . . . . . for rcwa mappings in sparse representation
##
InstallMethod( Modulus, "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0, f -> f!.modulus );
InstallMethod( Modulus, "for rcwa mappings in sparse rep. (RCWA)",
               true, [ IsRcwaMappingInSparseRep ], 0, f -> f!.modulus );

#############################################################################
##
#M  Coefficients( <f> ) . . . .  for rcwa mappings in standard representation
#M  Coefficients( <f> ) . . . . .  for rcwa mappings in sparse representation
##
InstallMethod( Coefficients, "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0, f -> f!.coeffs );
InstallMethod( Coefficients, "for rcwa mappings in sparse rep. (RCWA)",
               true, [ IsRcwaMappingInSparseRep ], 0, f -> f!.coeffs );

#############################################################################
##
#S  Methods for the attributes and properties derived from the coefficients.
##
#############################################################################

#############################################################################
##
#M  Multiplier( <f> ) . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( Multiplier, "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,
               f -> Lcm( UnderlyingRing( FamilyObj( f ) ),
                         List( f!.coeffs, c -> c[1] ) ) );
InstallMethod( Multiplier, "for rcwa mappings in sparse rep. (RCWA)",
               true, [ IsRcwaMappingInSparseRep ], 0,
               f -> Lcm( UnderlyingRing( FamilyObj( f ) ),
                         List( f!.coeffs, c -> c[3] ) ) );
InstallMethod( Multiplier, "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZInStandardRep ], 10,
               f -> Lcm( List( f!.coeffs, c -> c[1] ) ) );
InstallMethod( Multiplier, "for rcwa mappings of Z_(pi) (RCWA)", true,
               [ IsRcwaMappingOfZ_piInStandardRep ], 10,
               f -> Lcm( List( f!.coeffs,
                               c -> StandardAssociate(Source(f),c[1]) ) ) );

#############################################################################
##
#M  Divisor( <f> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( Divisor, "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,
               f -> Lcm( UnderlyingRing( FamilyObj( f ) ),
                         List( f!.coeffs, c -> c[3] ) ) );
InstallMethod( Divisor, "for rcwa mappings in sparse rep. (RCWA)",
               true, [ IsRcwaMappingInSparseRep ], 0,
               f -> Lcm( UnderlyingRing( FamilyObj( f ) ),
                         List( f!.coeffs, c -> c[5] ) ) );
InstallMethod( Divisor, "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZInStandardRep ], 0,
               f -> Lcm( Integers, List( f!.coeffs, c -> c[3] ) ) );

#############################################################################
##
#M  IsIntegral( <f> ) . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( IsIntegral, "for rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 0, f -> IsOne( Divisor( f ) ) );

#############################################################################
##
#M  IsBalanced( <f> ) . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( IsBalanced, "for rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 0,
               f -> Set( Factors( Multiplier( f ) ) )
                  = Set( Factors( Divisor( f ) ) ) );
InstallMethod( IsBalanced, "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZ ], 0,
               f -> Set( Factors( DeterminantMat( Multiplier( f ) ) ) )
                  = Set( Factors( Divisor( f ) ) ) );

#############################################################################
##
#M  PrimeSet( <f> ) . . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( PrimeSet, "for rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 0,

  function ( f )
    if   IsZero(Multiplier(f))
    then Error("PrimeSet: Multiplier must not be zero.\n"); fi;
    return Filtered( Union( Factors(Source(f),Modulus(f)),
                            Factors(Source(f),Multiplier(f)),
                            Factors(Source(f),Divisor(f)) ),
                     x -> IsIrreducibleRingElement( Source( f ), x ) );
  end );

InstallMethod( PrimeSet, "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZ ], 0,

  function ( f )
    if   IsZero(Multiplier(f))
    then Error("PrimeSet: Multiplier must not be zero.\n"); fi;
    return Filtered( Union( # Factors(DeterminantMat(Modulus(f))),
                            Factors(DeterminantMat(Multiplier(f))),
                            Factors(Divisor(f)) ), IsPrimeInt );
  end );

#############################################################################
##
#M  IsClassWiseTranslating( <f> ) . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( IsClassWiseTranslating,
               "for rcwa mappings in standard rep. (RCWA)", true,
               [ IsRcwaMappingInStandardRep ], 0,
               f -> ForAll(Coefficients(f),c->IsOne(c[1]) and IsOne(c[3])) );
InstallMethod( IsClassWiseTranslating,
               "for rcwa mappings in sparse rep. (RCWA)", true,
               [ IsRcwaMappingInSparseRep ], 0,
               f -> ForAll(Coefficients(f),c->IsOne(c[3]) and IsOne(c[5])) );

#############################################################################
##
#M  IsClassWiseOrderPreserving( <f> ) . for rcwa mappings of Z, Z^2 or Z_(pi)
##
InstallMethod( IsClassWiseOrderPreserving,
               "for rcwa mappings of Z or Z_(pi) in standard rep. (RCWA)", 
               true, [ IsRcwaMappingOfZOrZ_piInStandardRep ], 0,
               f -> ForAll( f!.coeffs, c -> c[ 1 ] > 0 ) );
InstallMethod( IsClassWiseOrderPreserving,
               "for rcwa mappings of Z or Z_(pi) in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZOrZ_piInSparseRep ], 0,
               f -> ForAll( f!.coeffs, c -> c[ 3 ] > 0 ) );
InstallMethod( IsClassWiseOrderPreserving,
               "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZInStandardRep ], 0,
               f -> ForAll( f!.coeffs, c -> DeterminantMat( c[ 1 ] ) > 0 ) );

#############################################################################
##
#M  ClassWiseOrderPreservingOn( <f> )   for rcwa mappings of Z, Z^2 or Z_(pi)
##
InstallMethod( ClassWiseOrderPreservingOn,
               "for rcwa mappings of Z or Z_(pi) in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZOrZ_piInStandardRep ], 0,
               f -> ResidueClassUnion( Source( f ), Modulus( f ),
                      Filtered( [ 0 .. Modulus( f ) - 1 ],
                                r -> Coefficients( f )[r+1][1] > 0 ) ) );
InstallMethod( ClassWiseOrderPreservingOn,
               "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               f -> Union( List( Filtered( f!.coeffs, c -> c[3] > 0 ),
                                 d -> ResidueClass( d[1], d[2] ) ) ) );
InstallMethod( ClassWiseOrderPreservingOn,
               "for rcwa mappings of Z^2 (RCWA)",
               true, [ IsRcwaMappingOfZxZ ], 0,
               f -> ResidueClassUnion( Source( f ), Modulus( f ),
                      AllResidues( Source( f ), Modulus( f ) )
                        {Filtered([ 1 .. DeterminantMat( Modulus( f ) ) ],
                        r -> DeterminantMat(Coefficients(f)[r][1]) > 0)} ) );

#############################################################################
##
#M  ClassWiseOrderReversingOn( <f> ) .  for rcwa mappings of Z, Z^2 or Z_(pi)
##
InstallMethod( ClassWiseOrderReversingOn,
               "for rcwa mappings of Z or Z_(pi) in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZOrZ_piInStandardRep ], 0,
               f -> ResidueClassUnion( Source( f ), Modulus( f ),
                      Filtered( [ 0 .. Modulus( f ) - 1 ],
                                r -> Coefficients( f )[r+1][1] < 0 ) ) );
InstallMethod( ClassWiseOrderReversingOn,
               "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               f -> Union( List( Filtered( f!.coeffs, c -> c[3] < 0 ),
                                 d -> ResidueClass( d[1], d[2] ) ) ) );
InstallMethod( ClassWiseOrderReversingOn,
               "for rcwa mappings of Z^2 (RCWA)",
               true, [ IsRcwaMappingOfZxZ ], 0,
               f -> ResidueClassUnion( Source( f ), Modulus( f ),
                      AllResidues( Source( f ), Modulus( f ) )
                        {Filtered([ 1 .. DeterminantMat( Modulus( f ) ) ],
                        r -> DeterminantMat(Coefficients(f)[r][1]) < 0)} ) );

#############################################################################
##
##M  ClassWiseConstantOn( <f> ) . . . .  for rcwa mappings of Z, Z^2 or Z_(pi)
##
InstallMethod( ClassWiseConstantOn,
               "for rcwa mappings of Z or Z_(pi) in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZOrZ_piInStandardRep ], 0,
               f -> ResidueClassUnion( Source( f ), Modulus( f ),
                      Filtered( [ 0 .. Modulus( f ) - 1 ],
                                r -> Coefficients( f )[r+1][1] = 0 ) ) );
InstallMethod( ClassWiseConstantOn,
               "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               f -> Union( List( Filtered( f!.coeffs, c -> c[3] = 0 ),
                                 d -> ResidueClass( d[1], d[2] ) ) ) );
InstallMethod( ClassWiseConstantOn,
               "for rcwa mappings of Z^2 (RCWA)",
               true, [ IsRcwaMappingOfZxZ ], 0,
               f -> ResidueClassUnion( Source( f ), Modulus( f ),
                      AllResidues( Source( f ), Modulus( f ) )
                        {Filtered([ 1 .. DeterminantMat( Modulus( f ) ) ],
                        r -> IsZero(Coefficients(f)[r][1]))} ) );

#############################################################################
##
#P  IsSignPreserving( <f> ) . . . . . . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( IsSignPreserving, "for rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ ], 0,

  function ( f )

    local  bound, ind;

    if not IsClassWiseOrderPreserving(f) then return false; fi;
    if   IsRcwaMappingStandardRep(f) then ind := 2;
    elif IsRcwaMappingSparseRep(f)   then ind := 4;
    else TryNextMethod(); fi;
    bound := Maximum(1,Maximum(List(Coefficients(f),c->AbsInt(c[ind]))));
    return Minimum([0..bound]^f) >= 0 and Maximum([-bound..-1]^f) < 0;
  end );

#############################################################################
##
#M  IncreasingOn( <f> ) . . . . . . . . .  for rcwa mappings in standard rep.
##
InstallMethod( IncreasingOn, "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )

    local  R, m, c, selection;

    R := Source(f); m := Modulus(f); c := Coefficients(f);
    if   IsRing(R) then
      selection := Filtered([1..NumberOfResidues(R,m)],
                            r -> NumberOfResidues(R,c[r][3])
                               < NumberOfResidues(R,c[r][1]));
    elif IsZxZ(R) then
      selection := Filtered([1..NumberOfResidues(R,m)],
                            r -> c[r][3]^2 < NumberOfResidues(R,c[r][1]));
    else TryNextMethod(); fi;
    return ResidueClassUnion(R,m,AllResidues(R,m){selection});
  end );

#############################################################################
##
#M  IncreasingOn( <f> ) . . . . . . . . for rcwa mappings of Z in sparse rep.
##
InstallMethod( IncreasingOn, "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,

  function ( f )
    if ValueOption("classes") = true then
      return Set(Filtered(f!.coeffs,c->AbsInt(c[3])>c[5]),
                 c->ResidueClass(c[1],c[2]));
    else
      return ResidueClassUnion(Integers,
                               List(Filtered(f!.coeffs,c->AbsInt(c[3])>c[5]),
                                    c->c{[1,2]}));
    fi;
  end );

#############################################################################
##
#M  DecreasingOn( <f> ) . . . . . . . . .  for rcwa mappings in standard rep.
##
InstallMethod( DecreasingOn, "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )

    local  R, m, c, selection;

    R := Source(f); m := Modulus(f); c := Coefficients(f);
    if   IsRing(R) then
      selection := Filtered([1..NumberOfResidues(R,m)],
                            r -> NumberOfResidues(R,c[r][3])
                               > NumberOfResidues(R,c[r][1]));
    elif IsZxZ(R) then
      selection := Filtered([1..NumberOfResidues(R,m)],
                            r -> c[r][3]^2 > NumberOfResidues(R,c[r][1]));
    else TryNextMethod(); fi;
    return ResidueClassUnion(R,m,AllResidues(R,m){selection});
  end );

#############################################################################
##
#M  DecreasingOn( <f> ) . . . . . . . . for rcwa mappings of Z in sparse rep.
##
InstallMethod( DecreasingOn, "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,

  function ( f )
    if ValueOption("classes") = true then
      return Set(Filtered(f!.coeffs,c->AbsInt(c[3])<c[5]),
                 c->ResidueClass(c[1],c[2]));
    else
      return ResidueClassUnion(Integers,
                               List(Filtered(f!.coeffs,c->AbsInt(c[3])<c[5]),
                                    c->c{[1,2]}));
    fi;
  end );

#############################################################################
##
#M  ShiftsUpOn( <f> )  . . . . . . . . . . . . . . . . for rcwa mappings of Z
##
InstallMethod( ShiftsUpOn, "for rcwa mappings of Z in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZInStandardRep ], 0,
               f -> ResidueClassUnion( Integers, Modulus(f),
                      Filtered( [0..Modulus(f)-1],
                                r -> Coefficients(f)[r+1]{[1,3]} = [1,1]
                                 and Coefficients(f)[r+1][2] > 0 ) ) );
InstallMethod( ShiftsUpOn, "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,

  function ( f )
    if ValueOption("classes") = true then
      return Set(Filtered(f!.coeffs,
                           c->c{[3,5]}=[1,1] and c[4]>0),
                  c->ResidueClass(c[1],c[2]));
    else
      return ResidueClassUnion(Integers,
                               List(Filtered(f!.coeffs,
                                             c->c{[3,5]}=[1,1] and c[4]>0),
                                    c->c{[1,2]}));
    fi;
  end );

#############################################################################
##
#M  ShiftsDownOn( <f> )  . . . . . . . . . . . . . . . for rcwa mappings of Z
##
InstallMethod( ShiftsDownOn,
               "for rcwa mappings of Z in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZInStandardRep ], 0,
               f -> ResidueClassUnion( Integers, Modulus(f),
                      Filtered( [0..Modulus(f)-1],
                                r -> Coefficients(f)[r+1]{[1,3]} = [1,1]
                                 and Coefficients(f)[r+1][2] < 0 ) ) );
InstallMethod( ShiftsDownOn, "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,

  function ( f )
    if ValueOption("classes") = true then
      return Set(Filtered(f!.coeffs,
                           c->c{[3,5]}=[1,1] and c[4]<0),
                  c->ResidueClass(c[1],c[2]));
    else
      return ResidueClassUnion(Integers,
                               List(Filtered(f!.coeffs,
                                             c->c{[3,5]}=[1,1] and c[4]<0),
                                    c->c{[1,2]}));
    fi;
  end );

#############################################################################
##
#M  MaximalShift( <f> )  . . . . . . . . . . . . . . . for rcwa mappings of Z
##
InstallMethod( MaximalShift,
               "for rcwa mappings of Z in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZInStandardRep ], 0,
               f -> Maximum( List( f!.coeffs, c -> AbsInt(c[2]) ) ) );
InstallMethod( MaximalShift,
               "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               f -> Maximum( List( f!.coeffs, c -> AbsInt(c[4]) ) ) );

#############################################################################
##
#M  LargestSourcesOfAffineMappings( <f> )  for rcwa mappings in standard rep.
##
InstallMethod( LargestSourcesOfAffineMappings,
               "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )

    local  R, m, c, r;

    R := Source(f);
    m := Modulus(f);
    c := Coefficients(f);
    r := AllResidues(R,m);

    return Set(EquivalenceClasses([1..NumberOfResidues(R,m)],i->c[i]),
               cl->ResidueClassUnion(R,m,r{cl}));
  end );

#############################################################################
##
#M  LargestSourcesOfAffineMappings( <f> ) .  for rcwa mappings in sparse rep.
##
InstallMethod( LargestSourcesOfAffineMappings,
               "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               f -> Set(EquivalenceClasses(f!.coeffs,c->c{[3..5]}),
                        cl->ResidueClassUnion(Integers,
                                              List(cl,c->c{[1,2]}))) );

#############################################################################
##
#M  FixedPointsOfAffinePartialMappings( <f> ) for rcwa mapping of Z or Z_(pi)
##
InstallMethod( FixedPointsOfAffinePartialMappings,
               "for rcwa mappings of Z or Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZOrZ_pi ], 0,

  function ( f )

    local  m, c, fixedpoints, r;

    if not IsRcwaMappingStandardRep(f) then f := StandardRep(f); fi;

    m := Modulus(f); c := Coefficients(f);
    fixedpoints := [];
    for r in [1..m] do
      if   c[r][1] = c[r][3]
      then if c[r][2] = 0 then fixedpoints[r] := Rationals;
                          else fixedpoints[r] := []; fi;
      else fixedpoints[r] := [ c[r][2]/(c[r][3]-c[r][1]) ]; fi;
    od;

    return fixedpoints;
  end );

#############################################################################
##
#M  ImageDensity( <f> ) . . . . . . . . .  for rcwa mappings in standard rep.
##
InstallMethod( ImageDensity, "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )

    local  R, c, m;

    R := Source(f); c := Coefficients(f);
    m := NumberOfResidues(R,Modulus(f));
    if   IsRing(R) then
      return Sum([1..m],r->NumberOfResidues(R,c[r][3])/
                           NumberOfResidues(R,c[r][1]))/m;
    elif IsZxZ(R) then
      return Sum([1..m],r->c[r][3]^2/NumberOfResidues(R,c[r][1]))/m;
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  ImageDensity( <f> ) . . . . . . . . . . . for rcwa mappings in sparse rep.
##
InstallMethod( ImageDensity, "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               f -> Sum(List(f!.coeffs,c->c[5]/(c[2]*c[3]))) );

#############################################################################
##
#M  DensityOfSetOfFixedPoints( <f> )  for rcwa mappings of Z in standard rep.
##
InstallMethod( DensityOfSetOfFixedPoints,
               "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZInStandardRep ], 0,
               f->Number(Coefficients(f),c->c=[1,0,1])/Mod(f) );

#############################################################################
##
#M  DensityOfSetOfFixedPoints( <f> )  . for rcwa mappings of Z in sparse rep.
##
InstallMethod( DensityOfSetOfFixedPoints,
               "for rcwa mappings in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               f->Sum(List(Filtered(Coefficients(f),c->c{[3..5]}=[1,0,1]),
                  c->1/c[2])) );

#############################################################################
##
#M  DensityOfSupport( <f> ) . . . . . . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( DensityOfSupport, "for rcwa mappings (RCWA)",
               true, [ IsRcwaMappingOfZ ], 0,
               f -> 1 - DensityOfSetOfFixedPoints( f ) );

#############################################################################
##
#M  Multpk( <f>, <p>, <k> ) . . . . . for rcwa mappings of Z in standard rep.
##
InstallMethod( Multpk, "for rcwa mappings of Z in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZInStandardRep, IsInt, IsInt ], 0,

  function ( f, p, k )

    local  m, c, res;

    m := Modulus(f); c := Coefficients(f);
    res := Filtered([0..m-1],r->PadicValuation(c[r+1][1]/c[r+1][3],p)=k);
    return ResidueClassUnion(Integers,m,res);
  end );

#############################################################################
##
#M  Multpk( <f>, <p>, <k> ) . . . . . . for rcwa mappings of Z in sparse rep.
##
InstallMethod( Multpk, "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep, IsInt, IsInt ], 0,

  function ( f, p, k )
    return ResidueClassUnion(Integers,
                             List(Filtered(f!.coeffs,
                                           c->PadicValuation(c[3]/c[5],p)=k),
                                  c->c{[1,2]}));
  end );

#############################################################################
##
#M  Multpk( <f>, <p>, <k> ) . . . . . . . . . . . .  for rcwa mappings of Z^2
##
InstallMethod( Multpk, "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZ, IsInt, IsInt ], 0,

  function ( f, p, k )

    local  R, m, c, r;

    R := Source(f); m := Modulus(f); c := Coefficients(f);
    r := Filtered([1..NumberOfResidues(R,m)],
                  i->PadicValuation(DeterminantMat(c[i][1])/c[i][3]^2,p)=k);
    return ResidueClassUnion(R,m,AllResidues(R,m){r});
  end );

#############################################################################
##
#M  MultDivType( <f> ) . . . . . . . . for rcwa mappings of Z in standard rep.
##
InstallMethod( MultDivType,
               "for rcwa mappings of Z in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZInStandardRep ], 0,
               f->List(Collected(List(Coefficients(f),c->c[1]/c[3])),
                       t->[t[1],t[2]/Mod(f)]) );

#############################################################################
##
#M  MultDivType( <f> ) . . . . . . . .  for rcwa mappings of Z in sparse rep.
##
InstallMethod( MultDivType,
               "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               f->List(EquivalenceClasses(f!.coeffs,c->c[3]/c[5]),
                       cl->[cl[1][3]/cl[1][5],Sum(List(cl,c->1/c[2]))]) );

#############################################################################
##
#M  MappedPartitions( <g> ) . . . . . . .  for rcwa mappings in standard rep.
##
InstallMethod( MappedPartitions, "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( g )

    local  P;

    P := AllResidueClassesModulo( Source(g), Mod(g) );
    return [ List(P,Density), List(P^g,Density) ];
  end );

#############################################################################
##
#M  MappedPartitions( <g> ) . . . . . . for rcwa mappings of Z in sparse rep.
##
InstallMethod( MappedPartitions,
               "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               g -> [List(g!.coeffs,c->1/c[2]),
                     List(g!.coeffs,c->c[5]/(c[2]*c[3]))] );

#############################################################################
##
#M  HashValueOfRcwaMapping( <f>, <m> ) . . . . . . . . for rcwa mappings of Z
##
InstallMethod( HashValueOfRcwaMapping,
               "for rcwa mappings of Z (RCWA)", ReturnTrue,
               [ IsRcwaMappingOfZ, IsPosInt ], 0,

  function ( f, m )

    local  c, n, max, i;

    if not IsRcwaMappingOfZInSparseRep(f)
      and not IsRcwaMappingOfZInStandardRep(f)
    then TryNextMethod(); fi;
    c := Coefficients(f); max := m^3; n := 1;
    for i in [1..Length(c)] do
      n := (n*c[i][1]+c[i][2])*c[i][3]+c[i][1];
      if Length(c[i]) = 5 then n := (n+c[i][4])*c[i][5]+c[i][3]; fi;
      if AbsInt(n) > max then break; fi;
    od;
    return n mod m + 1;
  end );

#############################################################################
##
#S  The support of an rcwa mapping. /////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  MovedPoints( <f> ) . . . . . . . . . . for rcwa mappings in standard rep.
##
##  The set of moved points (support) of the rcwa mapping <f>.
##
InstallMethod( MovedPoints,
               "for rcwa mappings in standard rep. (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )

    local  R, m, c, residues, indices,
           fixedpoint, fixedpoints, fixedline, fixedlines,
           A, b, d, mat, i, quiet;

    R := Source(f); m := Modulus(f); c := Coefficients(f);
    residues := AllResidues(R,m); 
    if   IsRcwaMappingOfZOrZ_pi(f)
    then indices := Filtered([1..Length(residues)],i->c[i]<>[1,0,1]);
    elif IsRcwaMappingOfZxZ(f)
    then indices := Filtered([1..Length(residues)],
                             i->c[i]<>[[[1,0],[0,1]],[0,0],1]);
    else indices := Filtered([1..Length(residues)],i->c[i]<>[1,0,1]*One(R));
    fi;
    quiet := ValueOption("BeQuiet") = true;
    fixedpoints := []; fixedlines := [];
    if IsRing(R) then
      for i in indices do
        if c[i]{[1,3]} <> [1,1] * One(R) then
          fixedpoint := c[i][2]/(c[i][3]-c[i][1]);
          if   fixedpoint in R and fixedpoint mod m = residues[i]
          then Add(fixedpoints,fixedpoint); fi;
        fi;
      od;
    elif IsZxZ(R) then
      for i in indices do
        if c[i]{[1,3]} <> [[[1,0],[0,1]],1] then
          A := c[i][1]; b := c[i][2]; d := c[i][3];
          mat := A - [[d,0],[0,d]];
          if DeterminantMat(mat) <> 0 then
            fixedpoint := -b/mat;
            if   fixedpoint in R and fixedpoint mod m = residues[i]
            then Add(fixedpoints,fixedpoint); fi;
          else
            fixedline := SolutionNullspaceIntMat(mat,-b); # (v,w): v+k*w
            if fixedline[1] <> fail then Add(fixedlines,fixedline); fi;
          fi;
        fi;
      od;
    else TryNextMethod(); fi;
    if fixedlines <> [] and not quiet then
      fixedlines := Set(fixedlines);
      Info(InfoWarning,1,"MovedPoints: Sorry -- Lines are not yet ",
           "implemented;\nthere are the following fixed lines ",
           "(as pairs (v,w): l = v+k*w):\n",fixedlines);
    fi;
    return ResidueClassUnion(R,m,residues{indices},[],fixedpoints);
  end );

#############################################################################
##
#M  MovedPoints( <f> ) . . . . . . . .  for rcwa mappings of Z in sparse rep.
##
InstallMethod( MovedPoints,
               "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,

  function ( f )

    local  S, classes, fixedpoints, fixedpoint, c;

    classes := []; fixedpoints := [];
    for c in f!.coeffs do
      if c{[3..5]} <> [1,0,1] then
        Add(classes,c{[1,2]});
        if c{[3,5]} <> [1,1] then
          fixedpoint := c[4]/(c[5]-c[3]);
          if   IsInt(fixedpoint) and fixedpoint mod c[2] = c[1]
          then Add(fixedpoints,fixedpoint); fi;
        fi;
      fi;
    od;
    S := ResidueClassUnion(Integers,classes,[],fixedpoints);
    return S;
  end );

#############################################################################
##
#M  NrMovedPoints( <obj> ) . . . . . . . . . . . . . . . . . . default method
##
InstallOtherMethod( NrMovedPoints, "default method (RCWA)", true,
                    [ IsObject ], 0, obj -> Size( MovedPoints( obj ) ) );

#############################################################################
##
#M  Support( <g> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( Support, "for rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 0, MovedPoints );

#############################################################################
##
#S  Restricting an rcwa mapping to a residue class union. ///////////////////
##
#############################################################################

#############################################################################
##
#M  RestrictedMapping( <f>, <S> ) for an rcwa mapping and a res.- class union
##
InstallMethod( RestrictedMapping,
               "for an rcwa mapping and a residue class union (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsResidueClassUnion ], 0,

  function ( f, S )

    local  R, mf, mS, m, resf, resS, resm, cf, cfS, fS, r, pos, idcoeff;

    if not IsRcwaMappingStandardRep(f) then f := StandardRep(f); fi;

    R := Source(f);
    if UnderlyingRing(FamilyObj(S)) <> R
      or IncludedElements(S) <> [] or ExcludedElements(S) <> []
      or not IsSubset(S,S^f)
    then TryNextMethod(); fi;
    mf := Modulus(f); mS := Modulus(S); m := Lcm(mf,mS);
    resf := AllResidues(R,mf); resS := Residues(S); resm := AllResidues(R,m);
    if   IsRing(R) then idcoeff := [1,0,1]*One(R);
    elif IsZxZ(R)  then idcoeff := [[[1,0],[0,1]],[0,0],1];
    else TryNextMethod(); fi;
    cf := Coefficients(f);
    cfS := ListWithIdenticalEntries(Length(resm),idcoeff);
    for pos in [1..Length(resm)] do
      r := resm[pos];
      if r mod mS in resS then
        cfS[pos] := cf[Position(resf,r mod mf)];
      fi;
    od;
    fS := RcwaMapping(R,m,cfS);
    return fS;
  end );

#############################################################################
##
#M  RestrictedMapping( <f>, <R> ) . . for an rcwa mapping and its full source
##
InstallMethod( RestrictedMapping,
               "for an rcwa mapping and its full source (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsDomain ], 0,

  function ( f, R )
    if R = Source(f) then return f; else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  RestrictedPerm( <g>, <S> ) . . . . . .  for an rcwa permutation and a set
##
InstallMethod( RestrictedPerm,
               "for an rcwa permutation and a set (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsListOrCollection ], 0,
               RestrictedMapping );

#############################################################################
##
#S  Computing images under rcwa mappings. ///////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  ImageElm( <f>, <n> ) . . . . . .  for an rcwa mapping of Z and an integer
##
##  Returns the image of the integer <n> under the rcwa mapping <f>.
##
InstallMethod( ImageElm,
               "for rcwa mapping of Z in standard rep. and integer (RCWA)",
               true, [ IsRcwaMappingOfZInStandardRep, IsInt ], 0,

  function ( f, n )

    local  m, c;

    m := f!.modulus; c := f!.coeffs[n mod m + 1];
    return (c[1] * n + c[2]) / c[3];
  end );

#############################################################################
##
#M  ImageElm( <f>, <n> ) . . . . . .  for an rcwa mapping of Z and an integer
##
InstallMethod( ImageElm,
               "for rcwa mapping of Z in sparse rep. and integer (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep, IsInt ], 0,

  function ( f, n )

    local  m, c;

    m := f!.modulus;
    c := First(f!.coeffs,c->n mod c[2] = c[1]);
    return (c[3] * n + c[4]) / c[5];
  end );

#############################################################################
##
#M  ImageElm( <f>, <v> ) . . . .  for an rcwa mapping of Z^2 and a row vector
##
##  Returns the image of the vector <v> in Z^2 under the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "for an rcwa mapping of Z^2 and a row vector (RCWA)", true,
               [ IsRcwaMappingOfZxZInStandardRep, IsRowVector ], 10,

  function ( f, v )

    local  R, m, c;

    R := Source(f); if not v in R then TryNextMethod(); fi;
    m := f!.modulus;
    c := f!.coeffs[PositionSorted(AllResidues(R,m),v mod m)];
    return (v * c[1] + c[2]) / c[3];
  end );

#############################################################################
##
#M  ImageElm( <f>, <n> ) . for an rcwa mapping of Z_(pi) and an el. of Z_(pi)
##
##  Returns the image of the element <n> of the ring Z_(pi) for suitable <pi>
##  under the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "for rcwa mapping of Z_(pi) and element of Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZ_piInStandardRep, IsRat ], 0,

  function ( f, n )

    local  m, c;

    if not n in Source(f) then TryNextMethod(); fi;
    m := f!.modulus; c := f!.coeffs[n mod m + 1];
    return (c[1] * n + c[2]) / c[3];
  end );

#############################################################################
##
#M  ImageElm( <f>, <p> ) for rcwa mapping of GF(q)[x] and element of GF(q)[x]
##
##  Returns the image of the polynomial <p> under the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "for rcwa mapping of GF(q)[x] and element of GF(q)[x] (RCWA)",
               true, [ IsRcwaMappingOfGFqxInStandardRep, IsPolynomial ], 0,

  function ( f, p )

    local  R, m, c, r;

    R := Source(f); if not p in R then TryNextMethod(); fi;
    m := f!.modulus; r := p mod m;
    c := f!.coeffs[PositionSorted(AllResidues(R,m),r)];
    return (c[1] * p + c[2]) / c[3];
  end );

#############################################################################
##
#M  \^( <n>, <f> ) . . . . . . . . . . for a ring element and an rcwa mapping
##
##  Returns the image of the ring element <n> under the rcwa mapping <f>. 
##
InstallMethod( \^, "for a ring element and an rcwa mapping (RCWA)",
               ReturnTrue, [ IsRingElement, IsRcwaMapping ], 0,
               function ( n, f ) return ImageElm( f, n ); end );
InstallMethod( \^, "for a row vector and an rcwa mapping of Z^2 (RCWA)",
               ReturnTrue, [ IsRowVector, IsRcwaMappingOfZxZ ], 0,
               function ( v, f ) return ImageElm( f, v ); end );
InstallMethod( \^, "for list of row vectors and rcwa mapping of Z^2 (RCWA)",
               ReturnTrue, [ IsList, IsRcwaMappingOfZxZ ], 10,

  function ( l, f )
    if not IsSubset( Source( f ), l ) then TryNextMethod( ); fi;
    return List( l, v -> ImageElm( f, v ) );
  end );

#############################################################################
##
#M  ImagesElm( <f>, <n> ) . . . . . .  for an rcwa mapping and a ring element
##
##  Returns the images of the ring element <n> under the rcwa mapping <f>.
##  For technical purposes, only.
##
InstallMethod( ImagesElm, "for an rcwa mapping and a ring element (RCWA)",
               true, [ IsRcwaMapping, IsRingElement ], 0,
               function ( f, n ) return [ ImageElm( f, n ) ]; end ); 
InstallMethod( ImagesElm, "for rcwa mapping of Z^2 and row vector (RCWA)",
               true, [ IsRcwaMappingOfZxZ, IsRowVector ], 0,
               function ( f, n ) return [ ImageElm( f, n ) ]; end ); 

#############################################################################
##
#M  ImagesSet( <f>, <S> ) . . . for an rcwa mapping and a residue class union
##
##  Returns the image of the set <S> under the rcwa mapping <f>.
##
##  The method rank offset SUM_FLAGS is to ensure that this method also gets
##  called for rcwa zero mappings, instead of a Library method which returns
##  the zero module.
##
InstallMethod( ImagesSet,
               "for an rcwa mapping and a residue class union (RCWA)",
               ReturnTrue, [ IsRcwaMappingInStandardRep,
                             IsCollection ], SUM_FLAGS,

  function ( f, S )

    local  R, c, m, cls, i;

    R := Source(f); if not IsSubset(R,S) then TryNextMethod(); fi;
    if IsList(S) then return Set(List(S,n->n^f)); fi;
    c := Coefficients(f); m := Modulus(f);
    cls := AllResidueClassesModulo(R,m);
    return Union(List([1..Length(cls)],
                      i->(Intersection(S,cls[i])*c[i][1]+c[i][2])/c[i][3]));
  end );

#############################################################################
##
#M  ImagesSet( <f>, <S> )  for an rcwa mapping of Z and a residue class union
##
##  Returns the image of the set <S> under the rcwa mapping <f> of Z which is
##  assumed to be in "sparse" representation.
##
##  For the reason of the method rank offset SUM_FLAGS, see above.
##
InstallMethod( ImagesSet,
               "for an rcwa mapping of Z and a residue class union (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZInSparseRep,
                             IsCollection ], SUM_FLAGS,

  function ( f, S )
    if not IsSubset(Integers,S) then TryNextMethod(); fi;
    if IsList(S) then return Set(List(S,n->n^f)); fi;
    return Union(List(f!.coeffs,
             c->(Intersection(S,ResidueClass(c[1],c[2]))*c[3]+c[4])/c[5]));
  end );

#############################################################################
##
#M  ImagesSet( <f>, <cl> ) . . . for an rcwa mapping of Z and a residue class
##
##  Returns the image of the residue class <cl> under the rcwa mapping <f>.
##  It is required that <f> is injective and in standard representation, and
##  that the modulus of <f> divides the modulus of <cl>.
##
##  The rank offset SUM_FLAGS is needed to override the default method.
##
InstallMethod( ImagesSet,
               "for an rcwa mapping of Z and a residue class (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZInStandardRep and IsInjective,
                             IsResidueClassUnionOfZ and IsResidueClass ],
               SUM_FLAGS,

  function ( f, cl )

    local  c;

    if IsResidueClassUnionOfZInClassListRep(cl) then
      if cl!.m mod f!.modulus <> 0 then TryNextMethod(); fi;
      c := f!.coeffs[(cl!.cls[1][1]) mod f!.modulus + 1];
      return ResidueClass(Integers,c[1]*cl!.m/c[3],
                                  (c[1]*cl!.cls[1][1]+c[2])/c[3]);
    elif IsResidueClassUnionInResidueListRep(cl) then
      if cl!.m mod f!.modulus <> 0 then TryNextMethod(); fi;
      c := f!.coeffs[(cl!.r[1]) mod f!.modulus + 1];
      return ResidueClass(Integers,c[1]*cl!.m/c[3],
                                  (c[1]*cl!.r[1]+c[2])/c[3]);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  ImagesSet( <f>, <cl> ) . . . for an rcwa mapping of Z and a residue class
##
##  Returns the image of the residue class <cl> under the rcwa mapping <f>
##  of Z. It is required that <f> is injective and in sparse representation,
##  and that <cl> lies in the source of one affine partial mapping of <f>.
##
##  The rank offset SUM_FLAGS is needed to override the default method.
##
InstallMethod( ImagesSet,
               "for an rcwa mapping of Z and a residue class (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZInSparseRep and IsInjective,
                             IsResidueClassUnionOfZ and IsResidueClass ],
               SUM_FLAGS,

  function ( f, cl )

    local  c;

    if IsResidueClassUnionOfZInClassListRep(cl) then
      c := First(f!.coeffs,
                    c->cl!.cls[1][1] mod c[2] = c[1] and cl!.m mod c[2] = 0);
      if c = fail then TryNextMethod(); fi;
      return ResidueClass(Integers,c[3]*cl!.m/c[5],
                                  (c[3]*cl!.cls[1][1]+c[4])/c[5]);
    elif IsResidueClassUnionInResidueListRep(cl) then
      c := First(f!.coeffs,
                    c->cl!.r[1] mod c[2] = c[1] and cl!.m mod c[2] = 0);
      if c = fail then TryNextMethod(); fi;
      return ResidueClass(Integers,c[3]*cl!.m/c[5],
                                  (c[3]*cl!.r[1]+c[4])/c[5]);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  ImagesSource( <f> ) . . . . . . . . . . . . . . . . . for an rcwa mapping
##
##  Returns the image of the rcwa mapping <f>.
##
InstallMethod( ImagesSource,
               "for an rcwa mapping and a residue class union (RCWA)",
               true, [ IsRcwaMapping ], 2 * SUM_FLAGS,
               f -> ImagesSet( f, Source( f ) ) );

#############################################################################
##
#M  \^( <S>, <f> ) . . . . . for a set or class partition and an rcwa mapping
##
##  Returns the image of the set or class partition <S> under the
##  rcwa mapping <f>.
##
##  The argument <S> can be: 
##
##  - A finite set of elements of the source of <f>.
##  - A residue class union of the source of <f>.
##  - A partition of the source of <f> into (unions of) residue classes.
##    In this case the <i>th element of the result is the image of <S>[<i>].
##
InstallMethod( \^,
               "for a set / class partition and an rcwa mapping (RCWA)",
               ReturnTrue, [ IsListOrCollection, IsRcwaMapping ], 20,

  function ( S, f )
    if   S in Source(f)
    then return ImageElm(f,S);
    elif IsSubset(Source(f),S)
    then return ImagesSet(f,S);
    elif IsList(S) and ForAll(S,set->IsSubset(Source(f),set))
    then return List(S,set->set^f);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  \^( <U>, <f> ) .  for union of res.-cl. with fixed rep's and rcwa mapping
##
##  Returns the image of the union <U> of residue classes of Z with fixed
##  representatives under the rcwa mapping <f>.
##
InstallMethod( \^,
               Concatenation("for a union of residue classes with fixed ",
                             "rep's and an rcwa mapping (RCWA)"), ReturnTrue,
               [ IsUnionOfResidueClassesOfZWithFixedRepresentatives,
                 IsRcwaMappingOfZ ], 0,

  function ( U, f )

    local  cls, abc, m, c, k, l;

    if not IsRcwaMappingStandardRep(f) then f := StandardRep(f); fi;
    m := Modulus(f); c := Coefficients(f);
    k := List(Classes(U),cl->m/Gcd(m,cl[1])); l := Length(k);
    cls := AsListOfClasses(U);
    cls := List([1..l],i->RepresentativeStabilizingRefinement(cls[i],k[i]));
    cls := Flat(List(cls,cl->AsListOfClasses(cl)));
    abc := List(cls,cl->c[1 + Classes(cl)[1][2] mod m]);
    cls := List([1..Length(cls)],i->(abc[i][1]*cls[i]+abc[i][2])/abc[i][3]);
    return RepresentativeStabilizingRefinement(Union(cls),0);
  end );

#############################################################################
##
#S  Computing preimages under rcwa mappings. ////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  PreImageElm( <f>, <n> ) . for a bijective rcwa mapping and a ring element
##
##  Returns the preimage of the ring element <n> under the bijective
##  rcwa mapping <f>.
##
InstallMethod( PreImageElm,
               "for a bijective rcwa mapping and a ring element (RCWA)",
               true, [ IsRcwaMapping and IsBijective, IsRingElement ], 0,

  function ( f, n )
    return n^Inverse( f );
  end );

#############################################################################
##
#M  PreImagesElm( <f>, <n> ) . . . . . for an rcwa mapping and a ring element
##
##  Returns the preimages of <n> under the rcwa mapping <f>. 
##
InstallMethod( PreImagesElm,
               "for an rcwa mapping and a ring element (RCWA)", ReturnTrue, 
               [ IsRcwaMappingInStandardRep, IsRingElement ], 0,

  function ( f, n )
    
    local  R, c, m, preimage, singletons, residues, n1, pre;

    R := Source(f); if not n in R then TryNextMethod(); fi;
    c := f!.coeffs; m := f!.modulus;
    preimage := []; singletons := [];
    residues := AllResidues(R,m);
    for n1 in [1..Length(residues)] do
      if not IsZero(c[n1][1]) then
        pre := (c[n1][3] * n - c[n1][2])/c[n1][1];
        if   pre in R and pre mod m = residues[n1]
        then Add(singletons,pre); fi;
      else
        if c[n1][2] = n then
          if   IsOne(m) then return R;
          else preimage := Union(preimage,ResidueClass(R,m,residues[n1])); fi;
        fi;
      fi;
    od;
    preimage := Union(preimage,singletons);
    return preimage;
  end );

#############################################################################
##
#M  PreImagesElm( <f>, <n> ) . . . .  for an rcwa mapping of Z and an integer
##
InstallMethod( PreImagesElm,
               "for an rcwa mapping of Z and an integer (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZInSparseRep, IsInt ], 0,

  function ( f, n )
    
    local  coeffs, preimage, singletons, c, pre;

    coeffs := f!.coeffs;
    preimage := []; singletons := [];
    for c in coeffs do
      if c[3] <> 0 then
        pre := (c[5] * n - c[4])/c[3];
        if   IsInt(pre) and pre mod c[2] = c[1]
        then Add(singletons,pre); fi;
      else
        if c[4] = n then
          if   c[2] = 1 then return Integers;
          else preimage := Union(preimage,ResidueClass(c[1],c[2])); fi;
        fi;
      fi;
    od;
    preimage := Union(preimage,singletons);
    return preimage;
  end );

#############################################################################
##
#M  PreImagesRepresentative( <f>, <n> ) . . for rcwa mapping and ring element
##
##  Returns a representative of the set of preimages of the integer <n> under
##  the rcwa mapping <f>. 
##
InstallMethod( PreImagesRepresentative,
               "for an rcwa mapping and a ring element (RCWA)",
               ReturnTrue, [ IsRcwaMappingInStandardRep, IsRingElement ], 0,

  function ( f, n )
    
    local  R, c, m, residues, n1, pre;

    R := Source(f); if not n in R then return fail; fi;
    c := f!.coeffs; m := f!.modulus;
    residues := AllResidues(R,m);
    for n1 in [1..Length(residues)] do
      if not IsZero(c[n1][1]) then
        pre := (n * c[n1][3] - c[n1][2])/c[n1][1];
        if pre in R and pre mod m = residues[n1] then return pre; fi;
      else
        if c[n1][2] = n then return residues[n1]; fi;
      fi;
    od;
    return fail;
  end );

#############################################################################
##
#M  PreImagesRepresentative( <f>, <n> ) . . for rcwa mapping of Z and integer
##
InstallMethod( PreImagesRepresentative,
               "for an rcwa mapping of Z and an integer (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZInSparseRep, IsInt ], 0,

  function ( f, n )
    
    local  coeffs, c, pre;

    coeffs := f!.coeffs;
    for c in coeffs do
      if c[3] <> 0 then
        pre := (n * c[5] - c[4])/c[3];
        if IsInt(pre) and pre mod c[2] = c[1] then return pre; fi;
      else
        if c[4] = n then return c[1]; fi;
      fi;
    od;
    return fail;
  end );

#############################################################################
##
#M  PreImagesSet( <f>, <R> ) . .  for an rcwa mapping and its underlying ring
##
##  Returns the source of the rcwa mapping <f>.
##  For technical purposes, only.
##
InstallMethod( PreImagesSet,
               "for an rcwa mapping and its underlying ring (RCWA)", true, 
               [ IsRcwaMapping, IsRing ], 0,

  function ( f, R )
    if   R = UnderlyingRing( FamilyObj( f ) )
    then return R; else TryNextMethod( ); fi;
  end );

#############################################################################
##
#M  PreImagesSet( <f>, <l> ) . . . . . . for an rcwa mapping and a finite set
##
##  Returns the preimage of the finite set <l> under the rcwa mapping <f>.
##
InstallMethod( PreImagesSet,
               "for an rcwa mapping and a finite set (RCWA)",
               true, [ IsRcwaMapping, IsList ], 0,

  function ( f, l )
    return Union( List( Set( l ), n -> PreImagesElm( f, n ) ) );
  end );

#############################################################################
##
#M  PreImagesSet( <f>, <S> ) .  for an rcwa mapping and a residue class union
##
##  Returns the preimage of the residue class union <S> under the
##  rcwa mapping <f>.
##
InstallMethod( PreImagesSet,
               "for an rcwa mapping and a residue class union (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsResidueClassUnion ], 0,

  function ( f, S )

    local  R, preimage, parts, premod, preres, rump,
           pre, pre2, im, diff, excluded, n;

    R := Source(f); if not IsSubset(R,S) then TryNextMethod(); fi;
    rump := ResidueClassUnion( R, Modulus(S), Residues(S) );
    premod := Modulus(f) * Divisor(f) * Modulus(S);
    preres := Filtered( AllResidues( R, premod ), n -> n^f in rump );
    parts := [ ResidueClassUnion( R, premod, preres ) ];
    Append( parts, List( IncludedElements(S), n -> PreImagesElm( f, n ) ) );
    preimage := Union( parts );
    excluded := ExcludedElements(S);
    for n in excluded do
      pre  := PreImagesElm( f, n );
      im   := ImagesSet( f, pre );
      pre2 := PreImagesSet( f, Difference( im, excluded ) );
      diff := Difference( pre, pre2 );
      if   not IsEmpty( diff )
      then preimage := Difference( preimage, diff ); fi;
    od;
    return preimage;
  end );

#############################################################################
##
#M  PreImagesSet( <f>, <S> ) .  for rcwa mapping of Z and residue class union
##
InstallMethod( PreImagesSet,
               "for an rcwa mapping of Z and a residue class union (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZInSparseRep,
                             IsResidueClassUnionOfZ ], 0,

  function ( f, S )

    local  coeffs, c, preimage, img, pre;

    coeffs   := f!.coeffs;
    preimage := [];

    for c in coeffs do
      if c[3] <> 0 then
        img := ResidueClass(Integers,c[3]*c[2]/c[5],(c[3]*c[1]+c[4])/c[5]);
        img := Intersection(img,S);
        pre := (c[5]*img-c[4])/c[3];
      else
        if c[4] in S then pre := ResidueClass(c[1],c[2]); else pre := []; fi;
      fi;
      preimage := Union(preimage,pre);
    od;

    return preimage;
  end );

#############################################################################
##
#M  PreImagesSet( <f>, <U> ) . . . . as above, but with fixed representatives
##
##  Returns the preimage of the union <U> of residue classes of Z with fixed
##  representatives under the rcwa mapping <f>.
##
InstallMethod( PreImagesSet,
               Concatenation("for an rcwa mapping of Z and a union of ",
                             "residue classes with fixed rep's (RCWA)"),
               ReturnTrue,
               [ IsRcwaMappingOfZ,
                 IsUnionOfResidueClassesOfZWithFixedRepresentatives ], 0,

  function ( f, U )

    local  preimage, cls, rep, m, minv, clm, k, l;

    if not IsRcwaMappingStandardRep(f) then f := StandardRep(f); fi;

    m := Modulus(f); minv := Multiplier(f) * m;
    k := List(Classes(U),cl->minv/Gcd(minv,cl[1])); l := Length(k);
    cls := AsListOfClasses(U);
    cls := List([1..l],i->RepresentativeStabilizingRefinement(cls[i],k[i]));
    cls := Flat(List(cls,cl->AsListOfClasses(cl)));
    rep := List(cls,cl->PreImagesElm(f,Classes(cl)[1][2]));
    cls := List(cls,cl->PreImagesSet(f,AsOrdinaryUnionOfResidueClasses(cl)));
    clm := AllResidueClassesModulo(Integers,m);
    cls := List(cls,cl1->List(clm,cl2->Intersection(cl1,cl2)));
    cls := List(cls,list->Filtered(list,cl->cl<>[]));
    cls := List([1..Length(cls)],
                i->List(cls[i],cl->[Modulus(cl),
                                    Intersection(rep[i],cl)[1]]));
    cls := Concatenation(cls);
    preimage := UnionOfResidueClassesWithFixedRepresentatives(Integers,cls);

    return RepresentativeStabilizingRefinement(preimage,0);
  end );

#############################################################################
##
#S  Testing an rcwa mapping for injectivity and surjectivity. ///////////////
##
#############################################################################

#############################################################################
##
#M  IsInjective( <f> ) . . . . . . . . . . . for rcwa mappings of Z or Z_(pi)
##
InstallMethod( IsInjective,
               "for rcwa mappings of Z or Z_(pi) (RCWA)", true,
               [ IsRcwaMappingOfZOrZ_piInStandardRep ], 0,

  function ( f )

    local  c, cInv, m, mInv, n, t, tm, tn, Classes, cl;

    if IsZero(Multiplier(f)) then return false; fi;
    if Product(PrimeSet(f)) > 30 then
      if Length(Set(List([-100..100],n->n^f))) < 201
      then return false; fi;
      if Length(Set(List([-1000..1000],n->n^f))) < 2001
      then return false; fi;
    fi;
    c := f!.coeffs; m := f!.modulus;
    cInv := [];
    mInv := Multiplier( f ) * m / Gcd( m, Gcd( List( c, t -> t[3] ) ) );
    for n in [ 1 .. m ] do
      t := [c[n][3], -c[n][2], c[n][1]]; if t[3] = 0 then return false; fi;
      tm := StandardAssociate(Source(f),c[n][1]) * m / Gcd(m,c[n][3]);
      tn := ((n - 1) * c[n][1] + c[n][2]) / c[n][3] mod tm;
      Classes := List([1 .. mInv/tm], i -> (i - 1) * tm + tn);
      for cl in Classes do
        if IsBound(cInv[cl + 1]) and cInv[cl + 1] <> t then return false; fi;
        cInv[cl + 1] := t;
      od;
    od;
    return true;
  end );

#############################################################################
##
#M  IsInjective( <f> ) . . . . . . . .  for rcwa mappings of Z in sparse rep.
##
InstallMethod( IsInjective,
               "for rcwa mappings of Z in sparse rep. (RCWA)", true,
               [ IsRcwaMappingOfZInSparseRep ], 0,

  function ( f )

    local  coeffs, imgs, c;

    if Multiplier(f) = 0 then return false; fi;

    coeffs := f!.coeffs;
    imgs   := List(coeffs,c->[(c[3]*c[1]+c[4])/c[5],c[3]*c[2]/c[5]]);
    return ForAll(Combinations(imgs,2),
                  c->(c[1][1]-c[2][1]) mod Gcd(c[1][2],c[2][2]) <> 0);
  end );

#############################################################################
##
#M  IsInjective( <f> ) . . . . . . . . . . . .  for rcwa mappings of GF(q)[x]
##
InstallMethod( IsInjective,
               "for rcwa mappings of GF(q)[x] (RCWA)", true,
               [ IsRcwaMappingOfGFqxInStandardRep ], 0,

  function ( f )

    local  c, cInv, m, mInv, d, dInv, R, q, x, respols, res, resInv, r, n,
           t, tm, tr, tn, Classes, cl, pos;

    if IsZero(Multiplier(f)) then return false; fi;
    R := UnderlyingRing(FamilyObj(f));
    q := Size(CoefficientsRing(R));
    x := IndeterminatesOfPolynomialRing(R)[1];
    c := f!.coeffs; m := f!.modulus;
    cInv := [];
    mInv := StandardAssociate( R,
              Multiplier( f ) * m / Gcd( m, Gcd( List( c, t -> t[3] ) ) ) );
    if mInv = 0 then return false; fi;
    d := DegreeOfLaurentPolynomial(m);
    dInv := DegreeOfLaurentPolynomial(mInv);
    res := AllGFqPolynomialsModDegree(q,d,x);
    respols := List([0..dInv], d -> AllGFqPolynomialsModDegree(q,d,x));
    resInv := respols[dInv + 1];
    for n in [ 1 .. Length(res) ] do
      r := res[n];
      t := [c[n][3], -c[n][2], c[n][1]];
      if IsZero(t[3]) then return false; fi;
      tm := StandardAssociate(Source(f),c[n][1]) * m / Gcd(m,c[n][3]);
      tr := (r * c[n][1] + c[n][2]) / c[n][3] mod tm;
      Classes := List(respols[DegreeOfLaurentPolynomial(mInv/tm) + 1],
                      p -> p * tm + tr);
      for cl in Classes do
        pos := Position(resInv,cl);
        if IsBound(cInv[pos]) and cInv[pos] <> t then return false; fi; 
        cInv[pos] := t;
      od;
    od;
    return true;
  end );

#############################################################################
##
#M  IsInjective( <f> ) . . . . . . . . . . . . . . . for rcwa mappings of Z^2
##
InstallMethod( IsInjective,
               "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZ ], 0,

  function ( f )

    local  R, c, m, det, imgs;

    R := Source(f); c := Coefficients(f); m := Modulus(f);

    if   DeterminantMat(Multiplier(f)) = 0 or ImageDensity(f) > 1
    then return false; fi;

    det := DeterminantMat(m);
    if  Length(Cartesian([0..RootInt(det,2)-1],[0..RootInt(det,2)-1])^f)
      < RootInt(det,2)^2
    then return false; fi;

    if ImageDensity(f) = 1 and IsSurjective(f) then return true; fi;

    imgs := LargestSourcesOfAffineMappings(f)^f;
    return ForAll( Combinations(imgs,2), pair -> Intersection(pair) = [] );

    return true;
  end );

#############################################################################
##
#M  IsSurjective( <f> ) . . . . . . . . . .  for rcwa mappings of Z or Z_(pi)
##
InstallMethod( IsSurjective,
               "for rcwa mappings of Z or Z_(pi) (RCWA)", true,
               [ IsRcwaMappingOfZOrZ_piInStandardRep ], 0, 

  function ( f )

    local  c, cInv, m, mInv, n, t, tm, tn, Classes, cl;

    c := f!.coeffs; m := f!.modulus;
    cInv := [];
    if ForAll(c, t -> t[1] = 0) then return false; fi;
    mInv := AbsInt(Lcm(Filtered(List(c,t->StandardAssociate(Source(f),t[1])),
                                k -> k <> 0 )))
                 * m / Gcd(m,Gcd(List(c,t->t[3])));
    for n in [1 .. m] do
      t := [c[n][3], -c[n][2], c[n][1]];
      if t[3] <> 0 then
        tm := StandardAssociate(Source(f),c[n][1]) * m / Gcd(m,c[n][3]);
        tn := ((n - 1) * c[n][1] + c[n][2]) / c[n][3] mod tm;
        Classes := List([1 .. mInv/tm], i -> (i - 1) * tm + tn);
        for cl in Classes do cInv[cl + 1] := t; od;
      fi;
    od;
    return ForAll([1..mInv], i -> IsBound(cInv[i]));
  end );

#############################################################################
##
#M  IsSurjective( <f> ) . . . . . . . . for rcwa mappings of Z in sparse rep.
##
InstallMethod( IsSurjective,
               "for rcwa mappings of Z in sparse rep. (RCWA)", true,
               [ IsRcwaMappingOfZInSparseRep ], 0, 

  function ( f )

    local  coeffs, imgs;

    coeffs := f!.coeffs;
    if IsInjective(f) then
      return Sum(List(coeffs,c->c[5]/(c[2]*AbsInt(c[3])))) = 1;
    else
      imgs := List(Filtered(coeffs,c->c[3]<>0),
                   c->ResidueClass((c[3]*c[1]+c[4])/c[5],(c[3]*c[2])/c[5]));
      return IsIntegers(Union(imgs));
    fi;
  end );

#############################################################################
##
#M  IsSurjective( <f> ) . . . . . . . . . . . . for rcwa mappings of GF(q)[x]
##
InstallMethod( IsSurjective,
               "for rcwa mappings of GF(q)[x] (RCWA)", true,
               [ IsRcwaMappingOfGFqxInStandardRep ], 0,
               
  function ( f )

    local  c, cInv, m, mInv, d, dInv, R, q, x,
           respols, res, resInv, r, n, t, tm, tr, tn, Classes, cl, pos;

    R := UnderlyingRing(FamilyObj(f));
    q := Size(CoefficientsRing(R));
    x := IndeterminatesOfPolynomialRing(R)[1];
    c := f!.coeffs; m := f!.modulus;
    cInv := [];
    if ForAll( c, t -> IsZero(t[1]) ) then return false; fi;
    mInv := Lcm(Filtered(List(c, t -> StandardAssociate(Source(f),t[1])),
                         k -> not IsZero(k) ))
          * m / Gcd(m,Gcd(List(c,t->t[3])));
    d := DegreeOfLaurentPolynomial(m);
    dInv := DegreeOfLaurentPolynomial(mInv);
    res := AllGFqPolynomialsModDegree(q,d,x);
    respols := List([0..dInv], d -> AllGFqPolynomialsModDegree(q,d,x));
    resInv := respols[dInv + 1];
    for n in [ 1 .. Length(res) ] do
      r := res[n];
      t := [c[n][3], -c[n][2], c[n][1]];
      if not IsZero(t[3]) then
        tm := StandardAssociate(Source(f),c[n][1]) * m / Gcd(m,c[n][3]);
        tr := (r * c[n][1] + c[n][2]) / c[n][3] mod tm;
        Classes := List(respols[DegreeOfLaurentPolynomial(mInv/tm) + 1],
                        p -> p * tm + tr);
        for cl in Classes do cInv[Position(resInv,cl)] := t; od;
      fi;
    od;
    return ForAll([1..Length(resInv)], i -> IsBound(cInv[i]));
  end );

############################################################################
##
#F  InjectiveAsMappingFrom( <f> ) . . . .  some set on which <f> is injective
##
InstallGlobalFunction( InjectiveAsMappingFrom,

  function ( f )

    local  R, m, base, pre, im, cl, imcl, overlap;

    if not IsRcwaMappingStandardRep(f) then f := StandardRep(f); fi;
    R := Source(f); if IsBijective(f) then return R; fi;
    m := Modulus(f); base := AllResidueClassesModulo(R,m);
    pre := R; im := [];
    for cl in base do
      imcl    := cl^f;
      overlap := Intersection(im,imcl);
      im      := Union(im,imcl);
      pre     := Difference(pre,Intersection(PreImagesSet(f,overlap),cl));
    od;
    return pre;
  end );

#############################################################################
##
#M  IsUnit( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallOtherMethod( IsUnit,
                    "for rcwa mappings (RCWA)",
                    true, [ IsRcwaMapping ], 0, IsBijective );

#############################################################################
##
#S  Computing pointwise sums of rcwa mappings. //////////////////////////////
##
#############################################################################

#############################################################################
##
#M  \+( <f>, <g> ) . . . . . . . . . . . for two rcwa mappings of Z or Z_(pi)
##
##  Returns the pointwise sum of the rcwa mappings <f> and <g>.
##
InstallMethod( \+,
               "for two rcwa mappings of Z or Z_(pi) (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZOrZ_piInStandardRep,
                 IsRcwaMappingOfZOrZ_piInStandardRep ], 0,

  function ( f, g )
    
    local  c1, c2, c3, m1, m2, m3, n, n1, n2, pi;

    c1 := f!.coeffs;  c2 := g!.coeffs;
    m1 := f!.modulus; m2 := g!.modulus;
    m3 := Lcm(m1, m2);

    c3 := [];
    for n in [0 .. m3 - 1] do
      n1 := n mod m1 + 1;
      n2 := n mod m2 + 1;
      Add(c3, [ c1[n1][1] * c2[n2][3] + c1[n1][3] * c2[n2][1],
                c1[n1][2] * c2[n2][3] + c1[n1][3] * c2[n2][2],
                c1[n1][3] * c2[n2][3] ]);
    od;

    if   IsRcwaMappingOfZ( f )
    then return RcwaMappingNC( c3 );
    else pi := NoninvertiblePrimes( Source( f ) );
         return RcwaMappingNC( pi, c3 );
    fi;
  end );

#############################################################################
##
#M  \+( <f>, <g> ) . . . . . . . .  for two rcwa mappings of Z in sparse rep.
##
##  Returns the pointwise sum of the rcwa mappings <f> and <g>.
##
InstallMethod( \+,
               "for two rcwa mappings of Z in sparse rep. (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZInSparseRep,
                 IsRcwaMappingOfZInSparseRep ], 0,

  function ( f, g )
    
    local  coeffs1, coeffs2, coeffs3, c1, c2, c3, r;

    coeffs1 := f!.coeffs; coeffs2 := g!.coeffs; coeffs3 := [];
    for c1 in coeffs1 do
      for c2 in coeffs2 do
        if (c1[1] - c2[1]) mod Gcd(c1[2],c2[2]) = 0 then
          r := ChineseRem([c1[2],c2[2]],[c1[1],c2[1]]);
          c3 := [ r, Lcm(c1[2],c2[2]),
                  c1[3]*c2[5] + c1[5]*c2[3],
                  c1[4]*c2[5] + c1[5]*c2[4],
                  c1[5]*c2[5] ];
          Add(coeffs3,c3);
        fi;
      od;
    od;

    return RcwaMappingNC( coeffs3 );
  end );

#############################################################################
##
#M  \+( <f>, <g> ) . . .  for rcwa mappings of Z: sparse rep. + standard rep.
#M  \+( <f>, <g> ) . . .  for rcwa mappings of Z: standard rep. + sparse rep.
##
##  Returns the pointwise sum of the rcwa mappings <f> and <g>.
##
InstallMethod( \+,
               "for rcwa mappings of Z: sparse rep. + standard rep. (RCWA)",
               IsIdenticalObj, [ IsRcwaMappingOfZInSparseRep,
                                 IsRcwaMappingOfZInStandardRep ], 0,
               function ( f, g ) return StandardRepresentation(f) + g; end );

InstallMethod( \+,
               "for rcwa mappings of Z: standard rep. + sparse rep. (RCWA)",
               IsIdenticalObj, [ IsRcwaMappingOfZInStandardRep,
                                 IsRcwaMappingOfZInSparseRep ], 0,
               function ( f, g ) return f + StandardRepresentation(g); end );

#############################################################################
##
#M  \+( <f>, <g> ) . . . . . . . . . . . .  for two rcwa mappings of GF(q)[x]
##
##  Returns the pointwise sum of the rcwa mappings <f> and <g>.
##
InstallMethod( \+,
               "for two rcwa mappings of GF(q)[x] (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfGFqxInStandardRep,
                 IsRcwaMappingOfGFqxInStandardRep ], 0,

  function ( f, g )
    
    local c, m, d, R, q, x, res, r, n1, n2;

    c := [f!.coeffs, g!.coeffs, []];
    m := [f!.modulus, g!.modulus, Lcm(f!.modulus,g!.modulus)];
    d := List(m, DegreeOfLaurentPolynomial);
    R := UnderlyingRing(FamilyObj(f));
    q := Size(CoefficientsRing(R));
    x := IndeterminatesOfPolynomialRing(R)[1];
    res := List(d, deg -> AllGFqPolynomialsModDegree(q,deg,x));

    for r in res[3] do
      n1 := Position(res[1], r mod m[1]);
      n2 := Position(res[2], r mod m[2]);
      Add(c[3], [ c[1][n1][1] * c[2][n2][3] + c[1][n1][3] * c[2][n2][1],
                  c[1][n1][2] * c[2][n2][3] + c[1][n1][3] * c[2][n2][2],
                  c[1][n1][3] * c[2][n2][3] ]);
    od;

    return RcwaMappingNC( q, m[3], c[3] );
  end );

#############################################################################
##
#M  AdditiveInverseOp( <f> ) . . . . . . . . . . . . . . .  for rcwa mappings
#M  AdditiveInverseOp( <f> ) . . . . .  for rcwa mappings of Z in sparse rep. 
##
##  Returns the pointwise additive inverse of rcwa mapping <f>.
##
InstallMethod( AdditiveInverseOp,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               f -> f * RcwaMappingNC( Source(f), One(Source(f)),
                                       [[-1,0,1]] * One(Source(f)) ) );

InstallMethod( AdditiveInverseOp,
               "for rcwa mappings of Z in sparse rep. (RCWA)", true,
               [ IsRcwaMappingOfZInSparseRep ], 0,
               f -> RcwaMappingNC(List(f!.coeffs,
                                       c->[c[1],c[2],-c[3],-c[4],c[5]])) );

#############################################################################
##
#M  \+( <f>, <n> ) . . . . . . . . . . for an rcwa mapping and a ring element
#M  \+( <f>, <n> ) . . for an rcwa mapping of Z in sparse rep. and an integer
#M  \+( <n>, <f> ) . . . . . . . . . . for a ring element and an rcwa mapping
##
##  Returns the pointwise sum of the rcwa mapping <f> and the constant
##  rcwa mapping with value <n>.
##
InstallMethod( \+,
               "for an rcwa mapping and a ring element (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsRingElement ], 0,

  function ( f, n )

    local  R;

    R := Source(f);
    if not n in R then TryNextMethod(); fi;
    return f + RcwaMapping(R,One(R),[[0,n,1]]*One(R));
  end );

InstallMethod( \+,
               "for rcwa mapping of Z in sparse rep. and integer (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZInSparseRep, IsInt ], 0,

  function ( f, n )
    return RcwaMappingNC(List(f!.coeffs,
                              c->[c[1],c[2],c[3],c[4]+n*c[5],c[5]]));
  end );

InstallMethod( \+, "for a ring element and an rcwa mapping (RCWA)",
               ReturnTrue, [ IsRingElement, IsRcwaMapping ], 0,
               function ( n, f ) return f + n; end );

#############################################################################
##
#M  \+( <f>, <v> ) . . . . . for rcwa mappings of Z^2, addition of a constant
##
InstallMethod( \+, "for an rcwa mappings of Z^2 and a row vector (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZxZ, IsRowVector ], 0,

  function ( f, v )

    local  coeffs, sum;

    if not v in Source(f) then TryNextMethod(); fi;

    coeffs := List(Coefficients(f),c->[c[1],c[2]+c[3]*v,c[3]]);
    sum    := RcwaMapping(Source(f),Modulus(f),coeffs);

    if   HasIsInjective(f) and IsInjective(f)
    then SetIsInjective(sum,true); fi;
    if   HasIsSurjective(f) and IsSurjective(f)
    then SetIsSurjective(sum,true); fi;

    return sum;
  end );

InstallMethod( \+, "for a row vector and an rcwa mapping (RCWA)",
               ReturnTrue, [ IsRowVector, IsRcwaMappingOfZxZ ], 0,
               function ( v, f ) return f + v; end );

#############################################################################
##
#S  Multiplying rcwa mappings. //////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . .  for two rcwa mappings of Z or Z_(pi)
##
##  Returns the product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for two rcwa mappings of Z or Z_(pi) (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZOrZ_piInStandardRep,
                 IsRcwaMappingOfZOrZ_piInStandardRep ], SUM_FLAGS,

  function ( g, f )

    local  fg, c1, c2, c3, m1, m2, m3, n, n1, n2, pi;

    if   ValueOption( "sparse" ) = true and Multiplier( f ) <> 0
    then TryNextMethod(); fi;

    c1 := f!.coeffs;  c2 := g!.coeffs;
    m1 := f!.modulus; m2 := g!.modulus;
    m3 := Gcd( Lcm( m1, m2 ) * Divisor( f ), m1 * m2 );

    if   ValueOption("RMPROD_NO_EXPANSION") = true
    then m3 := Maximum(m1,m2); fi;

    c3 := [];
    for n in [0 .. m3 - 1] do
      n1 := n mod m1 + 1;
      n2 := (c1[n1][1] * n + c1[n1][2])/c1[n1][3] mod m2 + 1;
      Add(c3, [ c1[n1][1] * c2[n2][1],
                c1[n1][2] * c2[n2][1] + c1[n1][3] * c2[n2][2],
                c1[n1][3] * c2[n2][3] ]);
    od;

    if   IsRcwaMappingOfZ(f) 
    then fg := RcwaMappingNC(c3);
    else pi := NoninvertiblePrimes(Source(f));
         fg := RcwaMappingNC(pi,c3);
    fi;

    if    HasIsInjective(f) and IsInjective(f)
      and HasIsInjective(g) and IsInjective(g)
    then SetIsInjective(fg,true); fi;

    if    HasIsSurjective(f) and IsSurjective(f)
      and HasIsSurjective(g) and IsSurjective(g)
    then SetIsSurjective(fg,true); fi;

    return fg;
  end );

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . for two rcwa mappings of Z, sparse rep.
##
##  Returns the product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for two rcwa mappings of Z, sparse rep. (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZInSparseRep,
                 IsRcwaMappingOfZInSparseRep ], SUM_FLAGS,

  function ( g, f )

    local  fg, coeffs, c1, c2, c, img, int, pre;

    coeffs := [];
    for c1 in f!.coeffs do
      img := [ (c1[3]*c1[1] + c1[4])/c1[5], c1[3]*c1[2]/c1[5] ];
      for c2 in g!.coeffs do
        if img[2] <> 0 then
          if ( c2[1] - img[1] ) mod Gcd( c2[2], img[2] ) = 0 then
            int := [ ChineseRem( [ c2[2], img[2] ], [ c2[1], img[1] ] ),
                     Lcm( c2[2], img[2] ) ];
            pre := [ (int[1]*c1[5] - c1[4])/c1[3], int[2]*c1[5]/c1[3] ];
            c := [ pre[1], pre[2], c1[3]*c2[3],
                                   c1[4]*c2[3] + c1[5]*c2[4],
                                   c1[5]*c2[5] ];
            Add(coeffs,c);
          fi;
        elif img[1] mod c2[2] = c2[1] then
          pre := [ c1[1], c1[2] ];
          c := [ pre[1], pre[2], c1[3]*c2[3],
                                 c1[4]*c2[3] + c1[5]*c2[4],
                                 c1[5]*c2[5] ];
          Add(coeffs,c);
        fi;
      od;
    od;

    fg := RcwaMappingNC(coeffs);

    if    HasIsInjective(f) and IsInjective(f)
      and HasIsInjective(g) and IsInjective(g)
    then SetIsInjective(fg,true); fi;

    if    HasIsSurjective(f) and IsSurjective(f)
      and HasIsSurjective(g) and IsSurjective(g)
    then SetIsSurjective(fg,true); fi;

    return fg;
  end );

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . . . . . . . sparse rep. * standard rep.
#M  CompositionMapping2( <g>, <f> ) . . . . . . . standard rep. * sparse rep.
##
##  Returns the product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for rcwa mappings of Z, sparse rep. * standard rep. (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZInStandardRep,
                 IsRcwaMappingOfZInSparseRep ], SUM_FLAGS,
               function ( g, f )
                 return CompositionMapping2(g,StandardRepresentation(f));
               end );

InstallMethod( CompositionMapping2,
               "for rcwa mappings of Z, standard rep. * sparse rep. (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZInSparseRep,
                 IsRcwaMappingOfZInStandardRep ], SUM_FLAGS,
               function ( g, f )
                 return CompositionMapping2(StandardRepresentation(g),f);
               end );

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . . . . . .  for two rcwa mappings of Z^2
##
##  Returns the product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for two rcwa mappings of Z^2 (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZxZInStandardRep,
                 IsRcwaMappingOfZxZInStandardRep ], SUM_FLAGS,

  function ( g, f )

    local  R, fg, c1, c2, c, m1, m2, m,
           res1, res2, res, r1, r2, r, i1, i2, i;

    if   ValueOption( "sparse" ) = true and not IsZero( Multiplier( f ) )
    then TryNextMethod(); fi;

    R := Source(f);

    c1 := Coefficients(f);  c2 := Coefficients(g);
    m1 := Modulus(f);       m2 := Modulus(g);

    m := List(c1,t->m2*t[1]^-1);
    for i in [1..Length(m)] do
      m[i] := m[i] * Lcm(List(Flat(m[i]),DenominatorRat));
    od; 
    m := Lcm(m1,Lcm(m)) * Divisor(f);

    res1 := AllResidues(R,m1);
    res2 := AllResidues(R,m2);
    res  := AllResidues(R,m);

    c := [];
    for r in res do
      r1 := r mod m1;
      i1 := Position(res1,r1);
      r2 := (r * c1[i1][1] + c1[i1][2])/c1[i1][3] mod m2;
      i2 := Position(res2,r2);
      Add(c, [ c1[i1][1] * c2[i2][1],
               c1[i1][2] * c2[i2][1] + c1[i1][3] * c2[i2][2],
               c1[i1][3] * c2[i2][3] ]);
    od;

    fg := RcwaMapping(R,m,c); # ... NC, once tested

    if    HasIsInjective(f) and IsInjective(f)
      and HasIsInjective(g) and IsInjective(g)
    then SetIsInjective(fg,true); fi;

    if    HasIsSurjective(f) and IsSurjective(f)
      and HasIsSurjective(g) and IsSurjective(g)
    then SetIsSurjective(fg,true); fi;

    return fg;
  end );

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . . . . for two rcwa mappings of GF(q)[x]
##
##  Returns the product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for two rcwa mappings of GF(q)[x] (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfGFqxInStandardRep,
                 IsRcwaMappingOfGFqxInStandardRep ], SUM_FLAGS,

  function ( g, f )

    local  fg, c, m, d, R, q, x, res, r, n1, n2;

    if   ValueOption( "sparse" ) = true and not IsZero( Multiplier( f ) )
    then TryNextMethod(); fi;

    c := [f!.coeffs, g!.coeffs, []];
    m := [f!.modulus, g!.modulus];
    m[3] := Minimum( Lcm( m[1], m[2] ) * Divisor( f ), m[1] * m[2] );
    d := List(m, DegreeOfLaurentPolynomial);
    R := UnderlyingRing(FamilyObj(f));
    q := Size(CoefficientsRing(R));
    x := IndeterminatesOfPolynomialRing(R)[1];
    res := List(d, deg -> AllGFqPolynomialsModDegree(q,deg,x));

    for r in res[3] do
      n1 := Position(res[1], r mod m[1]);
      n2 := Position(res[2],
                     (c[1][n1][1] * r + c[1][n1][2])/c[1][n1][3] mod m[2]);
      Add(c[3], [ c[1][n1][1] * c[2][n2][1],
                  c[1][n1][2] * c[2][n2][1] + c[1][n1][3] * c[2][n2][2],
                  c[1][n1][3] * c[2][n2][3] ]);
    od;

    fg := RcwaMappingNC( q, m[3], c[3] );

    if    HasIsInjective(f) and IsInjective(f)
      and HasIsInjective(g) and IsInjective(g)
    then SetIsInjective(fg,true); fi;

    if    HasIsSurjective(f) and IsSurjective(f)
      and HasIsSurjective(g) and IsSurjective(g)
    then SetIsSurjective(fg,true); fi;

    return fg;
  end );

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . . . . . for two rcwa mappings of a ring
##
##  Returns the product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first. The multiplier of <f> must not be zero.
##
##  This method performs better than the standard methods above if <f> and
##  <g> have only few different affine partial mappings. It is used in place
##  of the standard methods if the option "sparse" is set.
##
##  This method presently does not work for Z^2, thus for this case there is
##  a separate "sparse" method (see below).
##
InstallMethod( CompositionMapping2,
               "for two rcwa mappings of a ring (sparse case method) (RCWA)",
               IsIdenticalObj, [ IsRcwaMappingInStandardRep,
                                 IsRcwaMappingInStandardRep ], 0,

  function ( g, f )

    local  fg, R, mf, mg, m, resf, resg, res, cf, cg, c,
           affs_f, affs_g, affs, Pf, Pg, Pf_img, P, cl, cl1, cl2,
           aff, pre, img, rj, mj, rjpre, mjpre, rjimg, mjimg, pos, i, j, k;

    if IsZero(Multiplier(f)) then TryNextMethod(); fi;

    R := Source(f);
    if not IsRing(R) then TryNextMethod(); fi;

    mf   := Modulus(f);        mg   := Modulus(g);
    resf := AllResidues(R,mf); resg := AllResidues(R,mg);
    cf   := Coefficients(f);   cg   := Coefficients(g);

    Pf := LargestSourcesOfAffineMappings(f);
    Pg := LargestSourcesOfAffineMappings(g);

    affs_f := List(Pf,S->cf[First([1..Length(resf)],i->resf[i] in S)]);
    affs_g := List(Pg,S->cg[First([1..Length(resg)],i->resg[i] in S)]);

    Pf := List(Pf,AsUnionOfFewClasses); Pg := List(Pg,AsUnionOfFewClasses); 

    Pf_img := [];
    for i in [1..Length(Pf)] do
      Pf_img[i] := [];
      for cl in Pf[i] do
        rj := Residue(cl); mj := Modulus(cl);
        rjimg := (rj*affs_f[i][1]+affs_f[i][2])/affs_f[i][3];
        mjimg := affs_f[i][1]*mj/affs_f[i][3];
        img   := ResidueClass(R,mjimg,rjimg);
        Add(Pf_img[i],img);
      od;
    od;

    P := []; affs := [];
    for i in [1..Length(Pf_img)] do
      for cl1 in Pf_img[i] do
        for j in [1..Length(Pg)] do
          for cl2 in Pg[j] do
            cl  := Intersection(cl1,cl2);
            if cl = [] then continue; fi;
            aff := [affs_f[i][1]*affs_g[j][1],
                    affs_f[i][2]*affs_g[j][1]+affs_f[i][3]*affs_g[j][2],
                    affs_f[i][3]*affs_g[j][3]];
            pos := Position(affs,aff);
            if pos = fail then
              Add(affs,aff); Add(P,[]);
              pos := Length(affs);
            fi;
            rj := Residue(cl); mj := Modulus(cl);
            rjpre := (rj*affs_f[i][3]-affs_f[i][2])/affs_f[i][1];
            mjpre := affs_f[i][3]*mj/affs_f[i][1];
            pre   := ResidueClass(R,mjpre,rjpre);
            Add(P[pos],pre);
          od;
        od;
      od;
    od;

    m   := Lcm(List(Flat(P),Modulus));
    res := AllResidues(R,m);
    c   := ListWithIdenticalEntries(Length(res),[1,0,1]*One(R));

    for i in [1..Length(P)] do
      aff := affs[i];
      for cl in P[i] do
        rj := Residue(cl); mj := Modulus(cl);
        for k in [1..Length(res)] do
          if res[k] mod mj = rj then c[k] := aff; fi;
        od;
      od;
    od;

    fg := RcwaMappingNC(R,m,c);

    if    HasIsInjective(f) and IsInjective(f)
      and HasIsInjective(g) and IsInjective(g)
    then SetIsInjective(fg,true); fi;

    if    HasIsSurjective(f) and IsSurjective(f)
      and HasIsSurjective(g) and IsSurjective(g)
    then SetIsSurjective(fg,true); fi;

    return fg;
  end );

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . . . . . .  for two rcwa mappings of Z^2
##
##  Returns the product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first. The multiplier of <f> must not be zero.
##
##  This is the equivalent for rcwa mappings of Z^2 of the "sparse" method
##  above.
##
InstallMethod( CompositionMapping2,
               "for two rcwa mappings of a ring (sparse case method) (RCWA)",
               IsIdenticalObj, [ IsRcwaMappingOfZxZInStandardRep,
                                 IsRcwaMappingOfZxZInStandardRep ], 0,

  function ( g, f )

    local  fg, R, mf, mg, m, resf, resg, res, cf, cg, c,
           affs_f, affs_g, affs, Pf, Pg, Pf_img, P, S1, S2, I,
           aff, pre, ri, mi, pos, i, j;

    if IsZero(Multiplier(f)) then TryNextMethod(); fi;

    R := Source(f);

    mf   := Modulus(f);        mg   := Modulus(g);
    resf := AllResidues(R,mf); resg := AllResidues(R,mg);
    cf   := Coefficients(f);   cg   := Coefficients(g);

    Pf := LargestSourcesOfAffineMappings(f);
    Pg := LargestSourcesOfAffineMappings(g);

    affs_f := List(Pf,S->cf[First([1..Length(resf)],i->resf[i] in S)]);
    affs_g := List(Pg,S->cg[First([1..Length(resg)],i->resg[i] in S)]);

    Pf_img := List(Pf,S->S^f);

    P := []; affs := [];
    for i in [1..Length(Pf_img)] do
      S1 := Pf_img[i];
      for j in [1..Length(Pg)] do
        S2 := Pg[j];
        I := Intersection(S1,S2);
        if IsEmpty(I) then continue; fi;
        aff := [affs_f[i][1]*affs_g[j][1],
                affs_f[i][2]*affs_g[j][1]+affs_f[i][3]*affs_g[j][2],
                affs_f[i][3]*affs_g[j][3]];
        pos := Position(affs,aff);
        if pos = fail then
          Add(affs,aff); Add(P,[]);
          pos := Length(affs);
        fi;
        pre := (I*affs_f[i][3]-affs_f[i][2])*affs_f[i][1]^-1;
        P[pos] := Union(P[pos],pre);
      od;
    od;

    m   := Lcm(List(P,Modulus));
    res := AllResidues(R,m);
    c   := ListWithIdenticalEntries(Length(res),Zero(R));

    for i in [1..Length(P)] do
      aff := affs[i]; mi := Modulus(P[i]);
      for ri in Residues(P[i]) do
        for j in [1..Length(res)] do
          if res[j] mod mi = ri then c[j] := aff; fi;
        od;
      od;
    od;

    fg := RcwaMappingNC(R,m,c);

    if    HasIsInjective(f) and IsInjective(f)
      and HasIsInjective(g) and IsInjective(g)
    then SetIsInjective(fg,true); fi;

    if    HasIsSurjective(f) and IsSurjective(f)
      and HasIsSurjective(g) and IsSurjective(g)
    then SetIsSurjective(fg,true); fi;

    return fg;
  end );

#############################################################################
##
#M  \*( <f>, <g> ) . . . . . . . . . . . . . . . . . .  for two rcwa mappings
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( \*,
               "for two rcwa mappings (RCWA)",
               IsIdenticalObj, [ IsRcwaMapping, IsRcwaMapping ], 0,

  function ( f, g )
    return CompositionMapping( g, f );
  end );

#############################################################################
##
#M  \*( <n>, <f> ) . . . . . . . . . . for a ring element and an rcwa mapping
#M  \*( <n>, <f> ) . .  for an integer and an rcwa mapping of Z in sparse rep.
#M  \*( <f>, <n> ) . . . . . . . . . . for an rcwa mapping and a ring element
##
InstallMethod( \*,
               "for rcwa mappings, multiplication by a constant (RCWA)",
               ReturnTrue, [ IsRingElement, IsRcwaMappingInStandardRep ], 0,

  function ( n, f )
    if not n in Source(f) then TryNextMethod(); fi;
    return RcwaMapping(Source(f),Modulus(f),
                       List(Coefficients(f),c->[n*c[1],n*c[2],c[3]]));
  end );

InstallMethod( \*,
               "for an rcwa mapping of Z in sparse rep. & a constant (RCWA)",
               ReturnTrue, [ IsInt, IsRcwaMappingOfZInSparseRep ], 0,

  function ( n, f )
    if not n in Source(f) then TryNextMethod(); fi;
    return RcwaMapping(List(f!.coeffs,c->[c[1],c[2],n*c[3],n*c[4],c[5]]));
  end );

InstallMethod( \*, "for rcwa mappings, multiplication by a constant (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsRingElement ], 0,

  function ( f, n )
    if not n in Source(f) then TryNextMethod(); fi;
    return n * f;
  end );

#############################################################################
##
#M  \*( <f>, <mat> ) . . for rcwa mappings of Z^2, multiplication by a matrix
##
InstallMethod( \*,
               "for rcwa mappings of Z^2, multiplication by a matrix (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZxZ, IsMatrix ], 0,

  function ( f, mat )

    local  coeffs, product;

    if   DimensionsMat(mat) <> [2,2] or not ForAll(Flat(mat),IsInt)
    then TryNextMethod(); fi;

    coeffs  := List(Coefficients(f),c->[c[1]*mat,c[2]*mat,c[3]]);
    product := RcwaMapping(Source(f),Modulus(f),coeffs);

    if   DeterminantMat(mat) <> 0 and HasIsInjective(f) and IsInjective(f)
    then SetIsInjective(product,true); fi;

    return product;
  end );

#############################################################################
##
#M  \*( <n>, <f> ) . . for rcwa mappings of Z^2, multiplication by an integer
##
InstallMethod( \*,
               "for rcwa mappings of Z^2, multiplication by integer (RCWA)",
               ReturnTrue, [ IsInt, IsRcwaMappingOfZxZ ], 0,
               function ( n, f ) return f * [ [ n, 0 ], [ 0, n ] ]; end );

#############################################################################
##
#S  Technical functions for deriving names of powers from names of bases. ///
##
#############################################################################

#############################################################################
##
#F  NAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER( <name>, <n>, <order> )
##
##  Appends ^<n> to <name>, or multiplies an existing exponent by <n>.
##  Reduces the exponent modulo <order>, if known (i.e. <> fail).
##
BindGlobal( "NAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER",

  function ( name, n, order )

    local  strings, e;

    strings := SplitString(name,"^");
    if not IsSubset("-0123456789",strings[Length(strings)]) then
      e    := n;
    else
      e    := Int(strings[Length(strings)]) * n;
      name := JoinStringsWithSeparator(strings{[1..Length(strings)-1]},"^");
    fi;
    if order = fail or order = infinity then
      return Concatenation(name,"^",String(e));
    elif e mod order = 1 then
      return name;
    elif e mod order = 0 then
      return fail;
    else
      return Concatenation(name,"^",String(e mod order));
    fi;
  end );

#############################################################################
##
#F  LATEXNAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER( <name>, <n>, <order> )
##
##  Appends ^{<n>} to <name>, if <name> does not already include an exponent.
##  Reduces the exponent <n> modulo <order>, if known (i.e. <> fail).
##
BindGlobal( "LATEXNAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER",

  function ( name, n, order )

    local  strings, e;

    strings := SplitString(name,"^");
    if not IsSubset("-0123456789{}",strings[Length(strings)]) then
      e    := n;
    else
      e    := Int(Filtered(strings[Length(strings)],
                           ch->ch in "-0123456789")) * n;
      name := JoinStringsWithSeparator(strings{[1..Length(strings)-1]},"^");
    fi;
    if   Position(name,'_') <> fail and name[1] <> '{'
    then name := Concatenation("{",name,"}"); fi;
    if order = fail or order = infinity then
      if e in [2..9] then return Concatenation(name,"^",String(e));
                     else return Concatenation(name,"^{",String(e),"}"); fi;
    elif e mod order = 1 then
      return name;
    elif e mod order = 0 then
      return fail;
    else
      e := e mod order;
      if e in [2..9] then return Concatenation(name,"^",String(e));
                     else return Concatenation(name,"^{",String(e),"}"); fi;
    fi;
  end );

#############################################################################
##
#S  Computing inverses of rcwa permutations. ////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  InverseOp( <f> ) . . . . . . . . . . . . for rcwa mappings of Z or Z_(pi)
##
##  Returns the inverse mapping of the bijective rcwa mapping <f>.
##
InstallMethod( InverseOp,
               "for rcwa mappings of Z or Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZOrZ_piInStandardRep ], 0,
               
  function ( f )

    local  Result, order, c, cInv, m, mInv, n, t, tm, tn, Classes, cl, pi;

    if HasOrder(f) and Order(f) = 2 then return f; fi;

    c := f!.coeffs; m := f!.modulus;
    cInv := [];
    mInv := Multiplier( f ) * m / Gcd( List( c, t -> t[3] ) );
    for n in [ 1 .. m ] do
      t := [c[n][3], -c[n][2], c[n][1]]; if t[3] = 0 then return fail; fi;
      tm := StandardAssociate(Source(f),c[n][1]) * m / c[n][3];
      tn := ((n - 1) * c[n][1] + c[n][2]) / c[n][3] mod tm;
      Classes := List([1 .. mInv/tm], i -> (i - 1) * tm + tn);
      for cl in Classes do
        if IsBound(cInv[cl + 1]) and cInv[cl + 1] <> t then return fail; fi; 
        cInv[cl + 1] := t;
      od;
    od;

    if not ForAll([1..mInv], i -> IsBound(cInv[i])) then return fail; fi;

    if   IsRcwaMappingOfZ( f )
    then Result := RcwaMappingNC( cInv );
    else pi := NoninvertiblePrimes( Source( f ) );
         Result := RcwaMappingNC( pi, cInv );
    fi;

    SetInverse(f,Result); SetInverse(Result,f);
    SetIsBijective(f,true); SetIsBijective(Result,true);

    if HasOrder(f) then SetOrder(Result,Order(f)); order := Order(f);
                   else order := fail; fi;
    if HasBaseRoot(f) then
      SetBaseRoot(Result,BaseRoot(f));
      SetPowerOverBaseRoot(Result,-PowerOverBaseRoot(f));
    fi;
    if HasSmallestRoot(f) then
      SetSmallestRoot(Result,SmallestRoot(f));
      SetPowerOverSmallestRoot(Result,-PowerOverSmallestRoot(f));
    fi;
    if HasName(f) then
      SetName(Result,NAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                       Name(f),-1,order));
    fi;
    if HasLaTeXString(f) then
      SetLaTeXString(Result,LATEXNAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                            LaTeXString(f),-1,order));
    fi;

    return Result;
  end );

#############################################################################
##
#M  InverseOp( <f> ) . . . . . . . . .  for rcwa mappings of Z in sparse rep.
##
##  Returns the inverse mapping of the bijective rcwa mapping <f>.
##
InstallMethod( InverseOp,
               "for rcwa mappings of Z in sparse rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep ], 0,
               
  function ( f )

    local  inverse, order;

    if not IsBijective(f) then return fail; fi;
    if HasOrder(f) and Order(f) = 2 then return f; fi;

    inverse := RcwaMappingNC(List(f!.coeffs,c->
                 [(c[3]*c[1]+c[4])/c[5],c[3]*c[2]/c[5],c[5],-c[4],c[3]]));

    SetInverse(f,inverse); SetInverse(inverse,f);
    SetIsBijective(f,true); SetIsBijective(inverse,true);

    if HasOrder(f) then SetOrder(inverse,Order(f)); order := Order(f);
                   else order := fail; fi;
    if HasBaseRoot(f) then
      SetBaseRoot(inverse,BaseRoot(f));
      SetPowerOverBaseRoot(inverse,-PowerOverBaseRoot(f));
    fi;
    if HasSmallestRoot(f) then
      SetSmallestRoot(inverse,SmallestRoot(f));
      SetPowerOverSmallestRoot(inverse,-PowerOverSmallestRoot(f));
    fi;
    if HasName(f) then
      SetName(inverse,NAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                      Name(f),-1,order));
    fi;
    if HasLaTeXString(f) then
      SetLaTeXString(inverse,LATEXNAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                            LaTeXString(f),-1,order));
    fi;

    return inverse;
  end );

#############################################################################
##
#M  InverseOp( <f> ) . . . . . . . . . . . . . . . . for rcwa mappings of Z^2
##
##  Returns the inverse mapping of the bijective rcwa mapping <f>.
##
InstallMethod( InverseOp,
               "for rcwa mappings of Z^2 (RCWA)", true,
               [ IsRcwaMappingOfZxZInStandardRep ], 0,
               
  function ( f )

    local  R, result, m, c, mInv, cInv, res, clsimg, indimg, t, order, i, j;

    if HasOrder(f) and Order(f) = 2 then return f; fi;
    if not IsBijective(f) then return fail; fi;

    R := Source(f); m := Modulus(f); c := Coefficients(f);

    clsimg := AllResidueClassesModulo(R,m)^f;
    mInv   := Lcm(List(clsimg,Modulus));
    res    := AllResidues(R,mInv);
    cInv   := [];

    for i in [1..Length(clsimg)] do
      t := [c[i][3]*c[i][1]^-1,-c[i][2]*c[i][1]^-1,1];
      t := t * Lcm(List(Flat(t),DenominatorRat));
      indimg := Filtered([1..Length(res)],j->res[j] in clsimg[i]);
      for j in indimg do cInv[j] := t; od;
    od;

    result := RcwaMapping(R,mInv,cInv); # ... NC, once tested

    SetInverse(f,result); SetInverse(result,f);
    SetIsBijective(f,true); SetIsBijective(result,true);

    if HasOrder(f) then SetOrder(result,Order(f)); order := Order(f);
                   else order := fail; fi;
    if HasName(f) then
      SetName(result,NAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                       Name(f),-1,order));
    fi;
    if HasLaTeXString(f) then
      SetLaTeXString(result,LATEXNAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                            LaTeXString(f),-1,order));
    fi;

    return result;
  end );

#############################################################################
##
#M  InverseOp( <f> ) . . . . . . . . . . . . .  for rcwa mappings of GF(q)[x]
##
##  Returns the inverse mapping of the bijective rcwa mapping <f>.
##
InstallMethod( InverseOp,
               "for rcwa mappings of GF(q)[x] (RCWA)", true,
               [ IsRcwaMappingOfGFqxInStandardRep ], 0,
               
  function ( f )

    local  Result, order, c, cInv, m, mInv, d, dInv, R, q, x,
           respols, res, resInv, r, n, t, tm, tr, tn, Classes, cl, pos;

    if HasOrder(f) and Order(f) = 2 then return f; fi;

    R := UnderlyingRing(FamilyObj(f));
    q := Size(CoefficientsRing(R));
    x := IndeterminatesOfPolynomialRing(R)[1];
    c := f!.coeffs; m := f!.modulus;
    cInv := [];
    mInv := StandardAssociate( R,
              Multiplier( f ) * m / Gcd( m, Gcd( List( c, t -> t[3] ) ) ) );
    d := DegreeOfLaurentPolynomial(m);
    dInv := DegreeOfLaurentPolynomial(mInv);
    res := AllGFqPolynomialsModDegree(q,d,x);
    respols := List([0..dInv], d -> AllGFqPolynomialsModDegree(q,d,x));
    resInv := respols[dInv + 1];

    for n in [ 1 .. Length(res) ] do
      r := res[n];
      t := [c[n][3], -c[n][2], c[n][1]];
      if IsZero(t[3]) then return fail; fi;
      tm := StandardAssociate(Source(f),c[n][1]) * m / c[n][3];
      tr := (r * c[n][1] + c[n][2]) / c[n][3] mod tm;
      Classes := List(respols[DegreeOfLaurentPolynomial(mInv/tm) + 1],
                      p -> p * tm + tr);
      for cl in Classes do
        pos := Position(resInv,cl);
        if IsBound(cInv[pos]) and cInv[pos] <> t then return fail; fi; 
        cInv[pos] := t;
      od;
    od;

    if   not ForAll([1..Length(resInv)], i -> IsBound(cInv[i]))
    then return fail; fi;

    Result := RcwaMappingNC( q, mInv, cInv );

    SetInverse(f,Result); SetInverse(Result,f);
    SetIsBijective(f,true); SetIsBijective(Result,true);

    if HasOrder(f) then SetOrder(Result,Order(f)); order := Order(f);
                   else order := fail; fi;
    if HasName(f) then
      SetName(Result,NAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                       Name(f),-1,order));
    fi;
    if HasLaTeXString(f) then
      SetLaTeXString(Result,LATEXNAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                            LaTeXString(f),n,order));
    fi;

    return Result;
  end );

#############################################################################
##
#M  InverseGeneralMapping( <f> ) . . . . . . . . . . . . .  for rcwa mappings
##
##  Returns the inverse mapping of the bijective rcwa mapping <f>.
##
InstallMethod( InverseGeneralMapping,
               "for rcwa mappings (RCWA)",
               true, [ IsRcwaMapping ], 0,
              
  function ( f )
    if IsBijective(f) then return Inverse(f); else TryNextMethod(); fi;
  end );

#############################################################################
##
#S  Computing right inverses of injective rcwa mappings. ////////////////////
##
#############################################################################

#############################################################################
##
#M  RightInverse( <f> ) . . . . . . . . . . . . . for injective rcwa mappings
##
InstallMethod( RightInverse,
               "for injective rcwa mappings (RCWA)",
               true, [ IsRcwaMapping ], 0,

  function ( f )

    local  R, mf, cf, resf, inv, minv, cinv, resinv, imgs,
           r1, r2, pos1, pos2, idcoeff;

    if not IsInjective(f) then return fail; fi;
    if not IsRcwaMappingStandardRep(f) then f := StandardRep(f); fi;

    R := Source(f);
    if   IsRing(R) then idcoeff := [1,0,1] * One(R);
    elif IsZxZ(R)  then idcoeff := [[[1,0],[0,1]],[0,0],1];
    else TryNextMethod(); fi;
    mf := Modulus(f); cf := Coefficients(f);
    imgs := AllResidueClassesModulo(R,mf)^f;
    minv := Lcm(List(imgs,Modulus));
    cinv := ListWithIdenticalEntries(NumberOfResidues(R,minv),idcoeff);
    resf := AllResidues(R,mf); resinv := AllResidues(R,minv);
    for r1 in resf do
      pos1 := PositionSorted(resf,r1);
      for r2 in AsList(Intersection(resinv,imgs[pos1])) do
        pos2 := PositionSorted(resinv,r2);
        if   IsRing(R)
        then cinv[pos2] := [cf[pos1][3],-cf[pos1][2],cf[pos1][1]];
        else cinv[pos2] := [cf[pos1][3]*cf[pos1][1]^-1,
                           -cf[pos1][2]*cf[pos1][1]^-1,1];
             cinv[pos2] := cinv[pos2] * Lcm(List(Flat(cinv[pos2]),
                                                 DenominatorRat));
        fi;
      od;
    od;
    inv := RcwaMapping(R,minv,cinv);
    return inv;
  end );

#############################################################################
##
#M  RightInverse( <f> ) . . . . . . . . . .  for injective rcwa mappings of Z
##
InstallMethod( RightInverse,
               "for injective rcwa mappings of Z (RCWA)",
               true, [ IsRcwaMappingOfZ ], 0,

  function ( f )

    local  inv, mf, cf, minv, cinv, imgs, r1, r2;

    if not IsInjective(f) then return fail; fi;
    if not IsRcwaMappingStandardRep(f) then f := StandardRep(f); fi;

    mf := Modulus(f); cf := Coefficients(f);
    imgs := AllResidueClassesModulo(mf)^f;
    minv := Lcm(List(imgs,Modulus));
    cinv := List([1..minv],r->[1,0,1]); 
    for r1 in [1..mf] do
      for r2 in Intersection([0..minv-1],imgs[r1]) do
        cinv[r2+1] := [cf[r1][3],-cf[r1][2],cf[r1][1]];
      od;
    od;
    inv := RcwaMapping(cinv);
    return inv;
  end );

#############################################################################
##
#M  CommonRightInverse( <l>, <r> ) . . . . . . . . for two rcwa mappings of Z
##
InstallMethod( CommonRightInverse,
               "for two rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ, IsRcwaMappingOfZ ], 0,

  function ( l, r )

    local  d, imgl, imgr, coeffs, m, c, r1, r2;

    if not ForAll([l,r],IsInjective) or Intersection(Image(l),Image(r)) <> []
       or Union(Image(l),Image(r)) <> Integers
    then return fail; fi;

    if not IsRcwaMappingStandardRep(l) then l := StandardRep(l); fi;
    if not IsRcwaMappingStandardRep(l) then r := StandardRep(r); fi;

    imgl := AllResidueClassesModulo(Modulus(l))^l;
    imgr := AllResidueClassesModulo(Modulus(r))^r;

    m := Lcm(List(Concatenation(imgl,imgr),Modulus));

    coeffs := List([0..m-1],r1->[1,0,1]);

    for r1 in [0..Length(imgl)-1] do
      c := Coefficients(l)[r1+1];
      for r2 in Intersection(imgl[r1+1],[0..m-1]) do
        coeffs[r2+1] := [ c[3], -c[2], c[1] ];
      od;
    od;

    for r1 in [0..Length(imgr)-1] do
      c := Coefficients(r)[r1+1];
      for r2 in Intersection(imgr[r1+1],[0..m-1]) do
        coeffs[r2+1] := [ c[3], -c[2], c[1] ];
      od;
    od;

    d := RcwaMapping(coeffs);
    return d;

  end );

#############################################################################
##
#S  Computing conjugates and powers of rcwa mappings. ///////////////////////
##
#############################################################################

#############################################################################
##
#M  \^( <g>, <h> ) . . . . . . . . . . . . . . . . . .  for two rcwa mappings
##
##  Returns the conjugate of the rcwa mapping <g> under <h>,
##  i.e. <h>^-1*<g>*<h>.
##
InstallMethod( \^,
               "for two rcwa mappings (RCWA)",
               IsIdenticalObj, [ IsRcwaMapping, IsRcwaMapping ], 0,

  function ( g, h )

    local  f;

    if IsOne(h) then return g; fi;
    f := h^-1 * g * h;
    if f = g then return g; fi;
    if HasOrder (g) then SetOrder (f,Order (g)); fi;
    if HasIsTame(g) then SetIsTame(f,IsTame(g)); fi;
    if   HasStandardConjugate(g)
    then SetStandardConjugate(f,StandardConjugate(g)); fi;
    if   HasStandardizingConjugator(g)
    then SetStandardizingConjugator(f,h^-1*StandardizingConjugator(g)); fi;
    if HasSmallestRoot(g) and AbsInt(PowerOverSmallestRoot(g)) > 1 then
      SetSmallestRoot(f,SmallestRoot(g)^h);
      SetPowerOverSmallestRoot(f,PowerOverSmallestRoot(g));
    fi;
    return f;
  end );

#############################################################################
##
#M  IsCommuting( <g>, <h> ) . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( IsCommuting,
               "for rcwa mappings (RCWA)", IsIdenticalObj,
               [ IsRcwaMapping, IsRcwaMapping ], 0,

  function ( g, h )

    local  R, a, b;

    if g = h then return true; fi;
    if HasInverse(g) and h = Inverse(g) then return true; fi;

    R := Source(g);
    if   NumberOfResidues(R,Mod(h)) > NumberOfResidues(R,Mod(g))
    then a := g; b := h; else a := h; b := g; fi;
    if   not ForAll(AllResidues(R,Mod(a)),r->(r^a)^b=(r^b)^a)
    then return false; fi;

    return g*h = h*g;
  end );

#############################################################################
##
#M  \^( <perm>, <g> ) . . . . . .  for a permutation and an rcwa mapping of Z
##
##  Returns the conjugate of the GAP permutation <perm> under the
##  rcwa permutation <g>. The rcwa permutation <g> must not move any point
##  in the support of <perm> to a negative integer.
##
InstallMethod( \^,
               "for a permutation and an rcwa mapping of Z (RCWA)",
               ReturnTrue, [ IsPerm, IsRcwaMappingOfZ ], 0,

  function ( perm, g )

    local  cycs, cyc, h, i;

    if not IsBijective(g) then
      Error("<g> must be bijective.\n");
      return fail;
    fi;
    if not ForAll(MovedPoints(perm)^g,IsPosInt) then
      Info(InfoWarning,1,
           "Warning: GAP permutations can only move positive integers!");
      TryNextMethod();
    fi;
    cycs := List(Cycles(perm,MovedPoints(perm)),cyc->OnTuples(cyc,g));
    h := ();
    for cyc in cycs do
      for i in [2..Length(cyc)] do h := h * (cyc[1],cyc[i]); od;
    od;
    return h;
  end );

#############################################################################
##
#M  \^( <f>, <n> ) . . . . . . . . . . . . for an rcwa mapping and an integer
##
##  Returns the <n>-th power of the rcwa mapping <f>. 
##
InstallMethod( \^,
               "for an rcwa mapping and an integer (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsInt ], 0,

  function ( f, n )

    local  pow, e, name, latex;

    if ValueOption("UseKernelPOW") = true then TryNextMethod(); fi;

    if HasOrder(f) and Order(f) <> infinity then n := n mod Order(f); fi;

    if   n = 0 then return One(f);
    elif n = 1 then return f;
    else if n > 1 then pow := POW(f,n:UseKernelPOW);
                  else pow := POW(Inverse(f),-n:UseKernelPOW); fi;
    fi;

    if HasIsTame(f) then SetIsTame(pow,IsTame(f)); fi;

    if HasBaseRoot(f) then
      SetBaseRoot(pow,BaseRoot(f));
      SetPowerOverBaseRoot(pow,PowerOverBaseRoot(f)*n);
    fi;

    if HasSmallestRoot(f) then
      SetSmallestRoot(pow,SmallestRoot(f));
      SetPowerOverSmallestRoot(pow,PowerOverSmallestRoot(f)*n);
    fi;

    if HasOrder(f) then
      if Order(f) = infinity then SetOrder(pow,infinity); else
        SetOrder(pow,Order(f)/Gcd(Order(f),n));
      fi;
      if HasName(f) and HasIsTame(f) and IsTame(f) then
        name := NAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(Name(f),n,Order(f));
        if name <> fail then SetName(pow,name); fi;
      fi;
      if HasLaTeXString(f) then
        latex := LATEXNAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                   LaTeXString(f),n,Order(f));
        if latex <> fail then SetLaTeXString(pow,latex); fi;
      fi;
    fi;

    if   HasIsClassShift(f) and IsClassShift(f) and not IsOne(pow)
    then SetIsPowerOfClassShift(pow,true); fi;

    return pow;
  end );

#############################################################################
##
#S  Testing an rcwa mapping for tameness, and respected partitions. /////////
##
#############################################################################

#############################################################################
##
#M  IsTame( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( IsTame,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  gamma, delta, C, r, m, coeffs, cl, img,
           starttime, k, pow, exp, e;

    Info(InfoRCWA,3,"`IsTame' for an rcwa mapping <f> of ",
                    RingToString(Source(f)),".");

    if IsBijective(f) and HasOrder(f) and Order(f) <> infinity then
      Info(InfoRCWA,3,"IsTame: <f> has finite order, hence is tame.");
      return true;
    fi;

    if IsIntegral(f) then
      Info(InfoRCWA,3,"IsTame: <f> is integral, hence tame.");
      return true;
    fi;

    if IsRing(Source(f))
      and not IsSubset(Factors(Multiplier(f)),Factors(Divisor(f)))
    then
      Info(InfoRCWA,3,"IsTame: <f> is wild, by balancedness criterion.");
      if IsBijective(f) then SetOrder(f,infinity); fi;
      return false;
    fi;

    if IsBijective(f) and not IsBalanced(f) then
      Info(InfoRCWA,3,"IsTame: <f> is wild, by balancedness criterion.");
      SetOrder(f,infinity); return false;
    fi;

    if IsSurjective(f) and not IsInjective(f) then
      Info(InfoRCWA,3,"IsTame: <f> is surjective and not ",
                      "injective, hence wild.");
      return false;
    fi;

    if IsRcwaMappingOfZOrZ_pi(f) and IsBijective(f) then
      Info(InfoRCWA,3,"IsTame: sources-and-sinks criterion.");
      gamma := TransitionGraph(f,Modulus(f));
      for r in [1..Modulus(f)] do RemoveSet(gamma.adjacencies[r],r); od;
      delta := UnderlyingGraph(gamma);
      C := ConnectedComponents(delta);
      if Position(List(C,V->Diameter(InducedSubgraph(gamma,V))),-1) <> fail
      then
        Info(InfoRCWA,3,"IsTame: <f> is wild, ",
                        "by sources-and-sinks criterion.");
        SetOrder(f,infinity); return false;
      fi;
    fi;

    if IsBijective(f) then
      Info(InfoRCWA,3,"IsTame: loop criterion.");
      m := Modulus(f);
      if IsRcwaMappingOfZ(f) then
        starttime := Runtime();
        k := 1; pow := f;
        repeat
          if Loops(pow) <> [] then
            Info(InfoRCWA,3,"IsTame: <f>^",k," has loops, thus <f> ",
                            "is wild by loop criterion.");
            SetOrder(f,infinity); return false;
          fi;
          if IsIntegral(pow) then
            Info(InfoRCWA,3,"IsTame: <f>^",k," is integral, ",
                            "thus <f> is tame.");
            return true;
          fi;
          if   Mod(pow) < m or LogInt(Int(Mod(pow)/m),2) < k/6 - 1
          then break; fi; 
          if Runtime() - starttime > 10 * m then break; fi;
          starttime := Runtime();
          k := k + 1; pow := pow * f;
        until false;
      else
        for cl in AllResidueClassesModulo(Source(f),m) do
          img := cl^f;
          if img <> cl and Intersection(cl,img) <> [] then
            Info(InfoRCWA,3,"IsTame: <f> is wild, by loop criterion.");
            SetOrder(f,infinity); return false;
          fi;
        od;
      fi;
    fi;

    Info(InfoRCWA,3,"IsTame: `finite order or integral power' criterion.");
    pow := f;
    exp := [2,2,3,5,2,7,3,2,11,13,5,3,17,2,19,2,2,3,5,7,11,2,23]; e := 1;
    for e in exp do
      pow := pow^e;
      if IsIntegral(pow) then
        Info(InfoRCWA,3,"IsTame: <f> has a power which is integral, ",
                        "hence is tame.");
        return true;
      fi;
      if       IsRcwaMappingOfZOrZ_pi(f)
           and Modulus(pow) > Minimum(Modulus(f)^2,2^16)
        or IsRcwaMappingOfGFqx(f)
           and   DegreeOfLaurentPolynomial(Modulus(pow))
               > DegreeOfLaurentPolynomial(Modulus(f)) + 2
      then break; fi;
    od;

    if IsBijective(f) and Order(f) <> infinity then
      Info(InfoRCWA,3,"IsTame: <f> has finite order, hence is tame.");
      return true;
    fi;

    if HasIsTame(f) then return IsTame(f); fi;

    Info(InfoRCWA,3,"IsTame: Giving up.");
    TryNextMethod();

  end );

#############################################################################
##
#M  RespectedPartition( <sigma> ) . . . . .  for tame bijective rcwa mappings
##
InstallMethod( RespectedPartition,
               "for tame bijective rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 0,

  function ( sigma )
    if not IsBijective(sigma) then return fail; fi;
    return RespectedPartition( Group( sigma ) );
  end );

#############################################################################
##
#M  RespectsPartition( <sigma>, <P> ) . .  for rcwa mappings in standard rep.
##
InstallMethod( RespectsPartition,
               "for rcwa mappings in standard rep. (RCWA)",
               ReturnTrue, [ IsRcwaMappingInStandardRep, IsList ], 0,

  function ( sigma, P )

    local  R, cl, c, c_rest, pos, res, r, m;

    R := Source(sigma);
    if   not ForAll(P,cl->IsResidueClass(cl) and IsSubset(R,cl))
      or Union(P) <> R or Sum(List(P,Density)) <> 1
    then TryNextMethod(); fi;
    if Permutation(sigma,P) = fail then return false; fi;
    c   := Coefficients(sigma);
    res := AllResidues(R,Modulus(sigma));
    for cl in P do
      r      := Residue(cl);
      m      := Modulus(cl);
      pos    := Filtered([1..Length(res)],i->res[i] mod m = r);
      c_rest := c{pos};
      if Length(Set(c_rest)) > 1 then return false; fi;
    od;
    return true;
  end );

#############################################################################
##
#M  RespectsPartition( <sigma>, <P> ) . for rcwa mappings of Z in sparse rep.
##
InstallMethod( RespectsPartition,
               "for rcwa mappings of Z in sparse rep. (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZInSparseRep, IsList ], 0,

  function ( sigma, P )

    if   not ForAll(P,cl->IsResidueClass(cl) and IsSubset(Integers,cl))
      or Union(P) <> Integers or Sum(List(P,Density)) <> 1
    then TryNextMethod(); fi;

    if Permutation(sigma,P) = fail then return false; fi;

    return ForAll(P,cl->Length(Set(Filtered(sigma!.coeffs,
                  c -> (c[1]-Residue(cl)) mod Gcd(c[2],Modulus(cl)) = 0),
                  d -> d{[3..5]})) = 1);
  end );

#############################################################################
##
#M  PermutationOpNC( <sigma>, <P>, <act> ) . .  for rcwa map. and resp. part.
##
##  This method serves only as a placeholder for something better.
##
InstallMethod( PermutationOpNC,
               "for an rcwa mapping and a respected partition (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsList, IsFunction ], 0,

  function ( sigma, P, act )
    return PermutationOp(sigma,P,act); 
  end );

#############################################################################
##
#M  PermutationOpNC( <sigma>, <P>, <act> ) for rcwa map. of Z and resp. part.
##
InstallMethod( PermutationOpNC,
               "for an rcwa mapping of Z and a respected partition (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZInSparseRep,
                             IsList, IsFunction ], 0,

  function ( sigma, P, act )

    local  cls, imgs, coeffs, conj, cl, img, c, i;

    if Length(P) = 1 then TryNextMethod(); fi;
    cls    := List(P,cl->[cl!.r[1],cl!.m]);
    coeffs := sigma!.coeffs;
    conj   := SortingPerm(cls)^-1;
    cls    := Set(cls);
    imgs   := [];
    for i in [1..Length(cls)] do
      cl      := cls[i];
      c       := First(coeffs,c->cl[1] mod c[2] = c[1]);
      img     := [(c[3]*cl[1]+c[4])/c[5],c[3]*cl[2]/c[5]];
      img[1]  := img[1] mod img[2];
      imgs[i] := PositionSorted(cls,img);
    od;
    return PermList(imgs)^conj;
  end );

#############################################################################
##
#M  PermutationOpNC( <sigma>, <P>, <act> ) for rcwa map. of Z and resp. part.
##
InstallMethod( PermutationOpNC,
               "for an rcwa mapping of Z and a respected partition (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZInStandardRep,
                             IsList, IsFunction ], 0,

  function ( sigma, P, act )

    local  cls, imgs, m, coeffs, conj, cl, img, c, i;

    if Length(P) = 1 then TryNextMethod(); fi;
    cls    := List(P,cl->[cl!.r[1],cl!.m]);
    m      := sigma!.modulus;
    coeffs := sigma!.coeffs;
    conj   := SortingPerm(cls)^-1;
    cls    := Set(cls);
    imgs   := [];
    for i in [1..Length(cls)] do
      cl      := cls[i];
      c       := coeffs[cl[1] mod m + 1];
      img     := [(c[1]*cl[1]+c[2])/c[3],c[1]*cl[2]/c[3]];
      img[1]  := img[1] mod img[2];
      imgs[i] := PositionSorted(cls,img);
    od;
    return PermList(imgs)^conj;
  end );

#############################################################################
##
#M  Permuted( <l>, <perm> ) . . . . . . . . . . . . . . . . . fallback method
##
##  This method is used in particular in the case that <perm> is an rcwa
##  permutation and <l> is a respected partition of <perm>.
##
InstallOtherMethod( Permuted,
                    "fallback method (RCWA)", ReturnTrue,
                    [ IsList, IsMapping ], 0,

  function ( l, perm )
    return Permuted( l, Permutation( perm, l ) );
  end );

#############################################################################
##
#M  CompatibleConjugate( <g>, <h> ) . . . . . . .  for two rcwa mappings of Z
##
InstallMethod( CompatibleConjugate,
               "for two rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ, IsRcwaMappingOfZ ], 0,

  function ( g, h )

    local DividedPartition, Pg, Ph, PgNew, PhNew, lg, lh, l, tg, th,
          remg, remh, cycg, cych, sigma, c, m, i, r;

    DividedPartition := function ( P, g, t )

      local  PNew, rem, cyc, m, r;

      PNew := []; rem := P;
      while rem <> [] do
        cyc := Cycle(g,rem[1]);
        rem := Difference(rem,cyc);
        m := Modulus(cyc[1]); r := Residues(cyc[1])[1];
        PNew := Union(PNew,
                      Flat(List([0..t-1],
                                k->Cycle(g,ResidueClass(Integers,
                                                        t*m,k*m+r)))));
      od;
      return PNew;
    end;

    if   not ForAll([g,h],f->IsBijective(f) and IsTame(f))
    then return fail; fi;
    Pg := RespectedPartition(g); Ph := RespectedPartition(h);
    lg := Length(Pg); lh := Length(Ph);
    l := Lcm(lg,lh); tg := l/lg; th := l/lh;
    PgNew := DividedPartition(Pg,g,tg); PhNew := DividedPartition(Ph,h,th);
    c := []; m := Lcm(List(PhNew,Modulus));
    for i in [1..l] do
      for r in Filtered([0..m-1],s->s mod Modulus(PhNew[i])
                                        = Residues(PhNew[i])[1]) do
        c[r+1] := [  Modulus(PgNew[i]),
                     Modulus(PhNew[i])*Residues(PgNew[i])[1]
                   - Modulus(PgNew[i])*Residues(PhNew[i])[1],
                     Modulus(PhNew[i]) ];
      od;
    od;
    sigma := RcwaMapping(c);
    if   IsRcwaMappingSparseRep(g) and IsRcwaMappingSparseRep(h)
    then sigma := SparseRep(sigma); fi;
    return h^sigma;
  end );

#############################################################################
##
#S  Computing the order of an rcwa permutation. /////////////////////////////
##
#############################################################################

#############################################################################
##
#M  Order( <g> ) . . . . . . . . . . . . . . . .  for bijective rcwa mappings
##
InstallMethod( Order,
               "for bijective rcwa mappings (RCWA)",
               true, [ IsRcwaMapping ], 0,

  function ( g )

    local  P, k, p, gtilde, e, e_old, e_max, l, l_max, stabiter,
           loopcheckbound, n0, n, b1, b2, m1, m2, r, cycs, pow, exp, c, i;

    if   not IsBijective(g) 
    then Error("Order: <rcwa mapping> must be bijective"); fi;
    
    Info(InfoRCWA,3,"`Order' for an rcwa permutation <g> of ",
                    RingToString(Source(g)),".");

    if IsOne(g) then return 1; fi;

    if HasIsTame(g) and not IsTame(g) then
      Info(InfoRCWA,3,"Order: <g> is wild, hence has infinite order.");
      return infinity;
    fi;

    if IsRcwaMappingOfZ(g) then
      if IsClassWiseOrderPreserving(g) and Determinant(g) <> 0 then
        Info(InfoRCWA,3,"Order: <g> is class-wise order-preserving, ",
                        "but not in ker det.");
        Info(InfoRCWA,3,"       Hence <g> has infinite order.");
        return infinity;
      fi;
      if not IsIntegral(g) then
        loopcheckbound := ValueOption("loopcheckbound");
        if loopcheckbound = fail then
          loopcheckbound := RootInt(Mod(g),2) + 5; # necessary AT LEAST
        fi;
        pow := g;
        for k in [1..loopcheckbound] do
          if Loops(pow) <> [] then
            Info(InfoRCWA,3,"Order: <g>^",k," has loops, hence <g> ",
                            "has infinite order.");
            SetIsTame(g,false);
            return infinity;
          fi;
          if k < loopcheckbound then pow := pow * g; fi;
          if IsIntegral(pow) then break; fi;
        od;
      fi;
    fi;

    if not IsBalanced(g) then
      Info(InfoRCWA,3,"Order: <g> has infinite order ",
                      "by the balancedness criterion.");
      SetIsTame(g,false); return infinity;
    fi;

    if IsRcwaMappingOfZOrZ_piInStandardRep(g) then

      m1 := Mod(g); pow := g;
      exp := [2,2,3,5,2,7,3,2,11,13,5,3,17,19,2];
      for e in exp do
        c := Coefficients(pow); m2 := Modulus(pow);
        if m2 > 6 * m1 then break; fi;
        r := First([1..m2],i -> c[i] <> [1,0,1] and c[i]{[1,3]} = [1,1]
                            and c[i][2] mod m2 = 0);
        if r <> fail then
          Info(InfoRCWA,3,"Order: <g> has infinite order ",
                          "by the arithmetic progression criterion.");
          return infinity;
        fi;
        pow := pow^e; if IsOne(pow) then break; fi;
        if Loops(pow) <> [] then
          Info(InfoRCWA,3,"Order: <g>^",e," has loops, ",
                          "thus <g> has infinite order.");
          SetIsTame(g,false);
          return infinity;
        fi;
      od;

      Info(InfoRCWA,3,"Order: Looking for finite cycles ... ");

      e := 1; l_max := 2 * Mod(g)^2; e_max := 2^Mod(g); stabiter := 0;
      b1 := 2^64-1; b2 := b1^2;
      repeat
        n0 := Random(-b1,b1); n := n0; l := 0;
        repeat
          n := n^g;
          l := l + 1;
        until n = n0 or AbsInt(n) > b2 or l > l_max;
        if n = n0 then
          e_old := e; e := Lcm(e,l);
          if e > e_old then stabiter := 0; else stabiter := stabiter + 1; fi;
        else break; fi;
      until stabiter = 64 or e > e_max;
    
      if e <= e_max and stabiter = 64 then
        c := Reversed(CoefficientsQadic(e,2)); pow := g;
        for i in [2..Length(c)] do
          pow := pow^2;
          if Mod(pow) > Mod(g)^2 then break; fi;
          if c[i] = 1 then pow := pow * g; fi;
          if Mod(pow) > Mod(g)^2 then break; fi;
        od;
        if IsOne(pow) then SetIsTame(g,true); return e; fi;
      fi;

    else # for rcwa permutations of rings other than Z or Z_(pi)

      cycs := ShortCycles(g,AllResidues(Source(g),Modulus(g)),
                            NumberOfResidues(Source(g),Modulus(g)));
      if cycs <> [] then
        e := Lcm(List(cycs,Length));
        pow := g^e;
        if IsIntegral(pow) then SetIsTame(g,true); fi;
        if IsOne(pow) then SetIsTame(g,true); return e; fi;
      fi;

    fi;

    if IsRcwaMappingOfZxZ(g) then TryNextMethod(); fi;

    if not IsRcwaMappingOfZ(g) and not IsTame(g) then
      Info(InfoRCWA,3,"Order: <g> is wild, thus has infinite order.");
      return infinity;
    fi;

    Info(InfoRCWA,3,"Order: determine a respected partition <P> of <g>,");
    Info(InfoRCWA,3,"       and compute the order <k> of the permutation");
    Info(InfoRCWA,3,"       induced by <g> on <P> as well as the order");
    Info(InfoRCWA,3,"       of <g>^<k>.");

    P := RespectedPartition(g);

    k      := Order(Permutation(g,P));
    gtilde := g^k;

    if IsOne(gtilde) then return k; fi;

    if IsRcwaMappingOfZOrZ_pi(g) then
      if   not IsClassWiseOrderPreserving(gtilde) and IsOne(gtilde^2)
      then return 2*k; else return infinity; fi;
    fi;

    if IsRcwaMappingOfGFqxInStandardRep(g) then
      e := Lcm(List(Coefficients(gtilde),c->Order(c[1])));
      gtilde := gtilde^e;
      if IsOne(gtilde) then return k * e; fi;
      p := Characteristic(Source(g));
      gtilde := gtilde^p;
      if IsOne(gtilde) then return k * e * p; fi;
    fi;

    if IsRcwaMappingOfGFqxInSparseRep(g) then
      e := Lcm(List(Coefficients(gtilde),c->Order(c[3])));
      gtilde := gtilde^e;
      if IsOne(gtilde) then return k * e; fi;
      p := Characteristic(Source(g));
      gtilde := gtilde^p;
      if IsOne(gtilde) then return k * e * p; fi;
    fi;

    if IsRcwaMappingOfZxZInStandardRep(g) then
      if ForAny(Coefficients(gtilde),c->Order(c[1])=infinity) then
        return infinity;
      else
        e := Lcm(List(Coefficients(gtilde),c->Order(c[1])));
        gtilde := gtilde^e;
        if IsOne(gtilde) then return k * e; else return infinity; fi;
      fi;
    fi;

    Info(InfoRCWA,3,"Order: Giving up.");
    TryNextMethod();

  end );

#############################################################################
##
#M  Order( <g> ) . . . . . . . . . . . . . . . . . . .  for elements of CT(Z)
##
InstallMethod( Order,
               "for elements of CT(Z) (RCWA)", true, [ IsRcwaMappingOfZ ], 5,

  function ( g )

    local  cycs, density, lastdensity, pow, partsbound, modbound, lngbound, n;

    if   not IsRcwaMappingOfZ(g) or not IsBijective(g)
      or not IsSignPreserving(g) or ValueOption("new_order") <> true
    then TryNextMethod(); fi;

    if IsOne(g) then return 1; fi;
    if IsIntegral(g) then
      SetIsTame(g,true);
      return Lcm(List(Cycles(g,[0..Mod(g)-1]),Length));
    fi;
    if Loops(g) <> [] then
      SetIsTame(g,false); return infinity;
    fi;

    if not IsRcwaMappingInSparseRep(g) then g := SparseRep(g); fi;

    n := 1; pow := g; lastdensity := 0;
    partsbound := 16; modbound := 32; lngbound := 16;
    repeat
      n := n + 1;
      pow := pow * g;
      if IsOne(pow) then SetIsTame(g,true); return n; fi;
      if Loops(pow) <> [] then SetIsTame(g,false); return infinity; fi;
      if Length(Coefficients(pow)) > partsbound
        or n mod (RootInt(Mod(g),2) + 5) = 0
      then
        cycs := ShortResidueClassCycles(g,modbound,lngbound);
        density := Sum(Flat(cycs),Density);
        if density = 1 then
          SetIsTame(g,true);
          return Lcm(List(cycs,Length));
        fi;
        if density > lastdensity then
          partsbound := partsbound * 2;
          modbound := modbound * Maximum(PrimeSet(g));
        else
          partsbound := 4 * Length(Coefficients(pow));
          modbound := modbound * Minimum(PrimeSet(g));
        fi;
        lngbound := lngbound * 2;
        lastdensity := density;
      fi;
    until false;

  end );

#############################################################################
##
#S  Transition matrices and transition graphs. //////////////////////////////
##
#############################################################################

#############################################################################
##
#M  TransitionMatrix( <f>, <m> ) .  for rcwa mapping and nonzero ring element
##
InstallMethod( TransitionMatrix,
               "for an rcwa mapping and an element<>0 of its source (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsRingElement ], 0,

  function ( f, m )

    local  T, R, mTest, Resm, ResmTest, n, i, j;

    if IsZero(m) or not m in Source(f) then
      Error("usage: TransitionMatrix( <f>, <m> ),\nwhere <f> is an ",
            "rcwa mapping and <m> <> 0 lies in the source of <f>.\n");
    fi;
    R := Source(f); Resm := AllResidues(R,m);
    mTest := Modulus(f) * Lcm(m,Divisor(f));
    ResmTest := AllResidues(R,mTest);
    T := NullMat(Length(Resm),Length(Resm));
    for n in ResmTest do
      i := Position(Resm,n   mod m);
      j := Position(Resm,n^f mod m);
      T[i][j] := T[i][j] + 1;
    od;
    return List(T,l->l/Sum(l));
  end );

#############################################################################
##
#M  TransitionMatrix( <g> ) .  for rcwa permutations of Z, single-arg. method
##
InstallMethod( TransitionMatrix,
               "for rcwa permutations of Z, single-argument method (RCWA)",
               true, [ IsRcwaMappingOfZ and IsBijective ], 0,

  function ( g )

    local  cls, img, pre, int, M, d, i, j;

    if not IsRcwaMappingOfZInSparseRep(g) then g := SparseRep(g); fi;
    cls := List(Filtered(Coefficients(g),c->c{[3..5]}<>[1,0,1]),
                c->ResidueClass(c[1],c[2]));
    d := Length(cls);
    M := NullMat(d,d);
    for i in [1..d] do
      img := cls[i]^g;
      for j in [1..d] do
        int := Intersection(img,cls[j]);
        if int <> [] then
          pre := int^(g^-1);
          M[i][j] := Density(pre)/Density(cls[i]);
        fi;
      od;
    od;
    return M;
  end );

#############################################################################
##
#F  TransitionSets( <f>, <m> ) . . . . . . . . . . . .  set transition matrix
##
InstallGlobalFunction( TransitionSets,

  function ( f, m )

    local  M, R, res, cl, im, r, i, j;

    R   := Source(f);
    res := AllResidues(R,m);
    cl  := List(res,r->ResidueClass(R,m,r));
    M   := [];
    for i in [1..Length(res)] do
      im   := cl[i]^f;
      M[i] := List([1..Length(res)],j->Intersection(im,cl[j]));
    od;
    return M;
  end );

#############################################################################
##
#M  TransitionGraph( <f>, <m> ) . . . . . .  for rcwa mappings of Z or Z_(pi)
##
##  Returns the transition graph of <f> for modulus <m> as a GRAPE graph.
##
##  The vertices are labelled by 1..<m> instead of 0..<m>-1 (0 is identified
##  with 1, etc.) because in {\GAP}, permutations cannot move 0.
##
InstallMethod( TransitionGraph,
               "for rcwa mappings of Z or Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZOrZ_pi, IsPosInt ], 0,

  function ( f, m )

    local  M;

    M := TransitionMatrix(f,m); 
    return Graph(Group(()), [1..m], OnPoints,
                 function(i,j) return M[i][j] <> 0; end, true);
  end );

#############################################################################
##
#M  TransitionGraph( <f> )  .  for rcwa mappings of Z, single-argument method
##
InstallMethod( TransitionGraph,
               "for rcwa mappings of Z, single-argument method (RCWA)",
               true, [ IsRcwaMappingOfZ ], 0,

  function ( f )

    local  M, m;

    M := TransitionMatrix(f); m := Length(M);
    return Graph(Group(()), [1..m], OnPoints,
                 function(i,j) return M[i][j] <> 0; end, true);
  end );

#############################################################################
##
#M  OrbitsModulo( <f>, <m> ) . . . . . . . . for rcwa mappings of Z or Z_(pi)
##
InstallMethod( OrbitsModulo,
               "for rcwa mappings of Z or Z_(pi) (RCWA)", true,
               [ IsRcwaMappingOfZOrZ_pi, IsPosInt ], 0,

  function ( f, m )

    local  gamma, delta, C, r;

    gamma := TransitionGraph(f,m);
    for r in [1..m] do RemoveSet(gamma.adjacencies[r],r); od;
    delta := UnderlyingGraph(gamma);
    C := ConnectedComponents(delta);
    return Set(List(C,c->List(c,r->r-1)));
  end );

#############################################################################
##
#M  FactorizationOnConnectedComponents( <f>, <m> )
##
InstallMethod( FactorizationOnConnectedComponents,
               "for rcwa mappings of Z or Z_(pi) (RCWA)", true,
               [ IsRcwaMappingOfZOrZ_pi, IsPosInt ], 0,

  function ( f, m )

    local  factors, c, comps, comp, coeff, m_f, m_res, r;

    if not IsRcwaMappingStandardRep(f) then f := StandardRep(f); fi;
    c := Coefficients(f);
    comps := OrbitsModulo(f,m);
    m_f := Modulus(f); m_res := Lcm(m,m_f);
    factors := [];
    for comp in comps do
      coeff := List([1..m_res],i->[1,0,1]);
      for r in [0..m_res-1] do
        if r mod m in comp then coeff[r+1] := c[r mod m_f + 1]; fi;
      od;
      Add(factors,RcwaMapping(coeff));
    od;
    return Set(Filtered(factors,f->not IsOne(f)));
  end );

############################################################################
##
#M  Sources( <f> ) . . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( Sources,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  sources, comps, adj, res;

    res   := AllResidues(Source(f),Modulus(f));
    adj   := TransitionGraph(f,Modulus(f)).adjacencies;
    comps := List(STRONGLY_CONNECTED_COMPONENTS_DIGRAPH(adj),
                  comp->ResidueClassUnion(Source(f),Modulus(f),res{comp}));
    sources := Filtered(comps,comp ->    IsSubset(comp,PreImagesSet(f,comp))
                                     and IsSubset(comp^f,comp)
                                     and comp^f <> comp);
    return sources;
  end );

############################################################################
##
#M  Sinks( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( Sinks,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  sinks, comps, adj, res;

    res   := AllResidues(Source(f),Modulus(f));
    adj   := TransitionGraph(f,Modulus(f)).adjacencies;
    comps := List(STRONGLY_CONNECTED_COMPONENTS_DIGRAPH(adj),
                  comp->ResidueClassUnion(Source(f),Modulus(f),res{comp}));
    sinks := Filtered(comps,comp ->    IsSubset(PreImagesSet(f,comp),comp)
                                   and IsSubset(comp,comp^f)
                                   and comp <> comp^f);
    return sinks;
  end );

############################################################################
##
#M  Loops( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( Loops,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  cls, cl, img, loops;

    cls   := AllResidueClassesModulo(Source(f),Modulus(f));
    loops := [];
    for cl in cls do
      img := cl^f;
      if img <> cl and Intersection(img,cl) <> [] then Add(loops,cl); fi; 
    od;
    return loops;
  end );

############################################################################
##
#M  Loops( <f> ) . . . . . for bijective rcwa mappings of Z in standard rep.
##
InstallMethod( Loops,
               "for bijective rcwa mappings of Z in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZInStandardRep and IsBijective ], 0,

  function ( f )

    local  c, i, r, m, r_img, m_img, loops;

    m     := Mod(f);
    c     := Coefficients(f);
    loops := [];
    for r in [0..Mod(f)-1] do
      m_img := AbsInt(c[r+1][1]/c[r+1][3])*m;
      r_img := ((c[r+1][1]*r+c[r+1][2])/c[r+1][3]) mod m_img;
      if   [r_img,m_img] <> [r,m] and (r_img - r) mod Gcd(m,m_img) = 0
      then Add(loops,ResidueClass(r,m)); fi;
    od;
    if loops <> [] then SetIsTame(f,false); fi;
    return loops;
  end );

############################################################################
##
#M  Loops( <f> ) . . . . . . for bijective rcwa mappings of Z in sparse rep.
##
InstallMethod( Loops,
               "for bijective rcwa mappings of Z in standard rep. (RCWA)",
               true, [ IsRcwaMappingOfZInSparseRep and IsBijective ], 0,

  function ( f )

    local  coeffs, modulus, c, r, m, r_img, m_img, loops;

    modulus := Mod(f);
    coeffs  := f!.coeffs;
    loops   := [];
    for c in coeffs do
      r := c[1]; m := c[2];
      m_img := AbsInt(c[3]*c[2]/c[5]);
      r_img := ((c[3]*r+c[4])/c[5]) mod m_img;
      if    [r_img,m_img] <> [r,m]
        and (r_img - r) mod Gcd(m,m_img) = 0
      then Add(loops,ResidueClass(r,m)); fi;
    od;
    if loops <> [] then SetIsTame(f,false); fi;
    return loops;
  end );

############################################################################
##
#M  Loops( <f> ) . . . . . . . . . . for bijective rcwa mappings of GF(q)[x]
##
InstallMethod( Loops,
               "for bijective rcwa mappings of GF(q)[x] (RCWA)", true,
               [ IsRcwaMappingOfGFqxInStandardRep and IsBijective ], 0,

  function ( f )

    local  R, m, c, res, r, r_img, m_img, loops, i;

    R     := Source(f);
    m     := Mod(f);
    c     := Coefficients(f);
    res   := AllResidues(R,m);
    loops := [];
    for i in [1..Length(res)] do
      r     := res[i];
      m_img := (c[i][1]/c[i][3])*m;
      r_img := ((c[i][1]*r+c[i][2])/c[i][3]) mod m_img;
      if   [r_img,m_img] <> [r,m] and IsZero((r_img - r) mod Gcd(R,m,m_img))
      then Add(loops,ResidueClass(R,m,r)); fi;
    od;
    if loops <> [] then SetIsTame(f,false); fi;
    return loops;
  end );

#############################################################################
##
#S  Trajectories. ///////////////////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  Trajectory( <f>, <n>, <length> )
##
InstallOtherMethod( Trajectory,
                    "for function, start point and length (RCWA)",
                    ReturnTrue, [ IsFunction, IsObject, IsPosInt ], 0,

  function ( f, n, length )

    local  l, i;

    l := [n];
    for i in [2..length] do
      n := f(n);
      Add(l,n);
    od;
    return l;
  end );

#############################################################################
##
#M  Trajectory( <f>, <n>, <terminal> )
##
InstallOtherMethod( Trajectory,
                    "for function, start point and terminal set (RCWA)",
                    ReturnTrue, [ IsFunction, IsObject, IsListOrCollection ],
                    0,

  function ( f, n, terminal )

    local  l, i;

    l := [n];
    while not n in terminal do
      n := f(n);
      Add(l,n);
    od;
    return l;
  end );

#############################################################################
##
#M  Trajectory( <f>, <n>, <halt> )
##
InstallOtherMethod( Trajectory,
                    "for function, start point and halting criterion (RCWA)",
                    ReturnTrue, [ IsFunction, IsObject, IsFunction ], 0,

  function ( f, n, halt )

    local  l, i;

    l := [n];
    while not halt(n) do
      n := f(n);
      Add(l,n);
    od;
    return l;
  end );

#############################################################################
##
#M  Trajectory( <f>, <n>, <length> ) . . . . . . . . . for rcwa mappings, (1)
##
InstallMethod( Trajectory,
               "for an rcwa mapping, given number of iterates (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsObject, IsPosInt ], 0,

  function ( f, n, length )

    local  seq, step, action;

    if   not (n in Source(f) or IsSubset(Source(f),n))
    then TryNextMethod(); fi;
    action := GetOption("Action",OnPoints,IsFunction);
    seq := [n];
    for step in [1..length-1] do
      n := action(n,f);
      Add(seq,n);
    od;
    return seq;
  end );

#############################################################################
##
#M  Trajectory( <f>, <n>, <length>, <m> ) . . . . . .  for rcwa mappings, (2)
##
InstallMethod( Trajectory,
               Concatenation("for an rcwa mapping, given number of ",
                             "iterates (mod <m>) (RCWA)"), ReturnTrue,
               [ IsRcwaMapping, IsObject, IsPosInt, IsRingElement ], 0,

  function ( f, n, length, m )

    local  seq, step, action;

    if   not (n in Source(f) or IsSubset(Source(f),n)) or IsZero(m)
    then TryNextMethod(); fi;
    action := GetOption("Action",OnPoints,IsFunction);
    seq := [n mod m];
    for step in [1..length-1] do
      n := action(n,f);
      Add(seq,n mod m);
    od;
    return seq;
  end );

#############################################################################
##
#M  Trajectory( <f>, <n>, <terminal> ) . . . . . . . . for rcwa mappings, (3)
##
InstallMethod( Trajectory,
               "for an rcwa mapping, until a given set is entered (RCWA)",
               ReturnTrue,
               [ IsRcwaMapping, IsObject, IsListOrCollection ], 0,

  function ( f, n, terminal )

    local  seq, action;

    if   not (n in Source(f) or IsSubset(Source(f),n))
    then TryNextMethod(); fi;
    action := GetOption("Action",OnPoints,IsFunction);
    seq := [n];
    if   IsListOrCollection(n) or not IsListOrCollection(terminal)
    then terminal := [terminal]; fi;
    while not n in terminal do
      n := action(n,f);
      Add(seq,n);
    od;
    return seq;
  end );

#############################################################################
##
#M  Trajectory( <f>, <n>, <terminal>, <m> ) . . . . .  for rcwa mappings, (4)
##
InstallMethod( Trajectory,
               Concatenation("for an rcwa mapping, until a given set i",
                             "s entered, (mod <m>) (RCWA)"), ReturnTrue,
               [ IsRcwaMapping, IsObject,
                 IsListOrCollection, IsRingElement ], 0,

  function ( f, n, terminal, m )

    local  seq, action;

    if   not (n in Source(f) or IsSubset(Source(f),n)) or IsZero(m)
    then TryNextMethod(); fi;
    action := GetOption("Action",OnPoints,IsFunction);
    seq := [n mod m];
    if   IsListOrCollection(n) or not IsListOrCollection(terminal)
    then terminal := [terminal]; fi;
    while not n in terminal do
      n := action(n,f);
      Add(seq,n mod m);
    od;
    return seq;
  end );

############################################################################
##
#M  Trajectory( <f>, <n>, <length>,   <whichcoeffs> ) for rcwa mappings, (5)
#M  Trajectory( <f>, <n>, <terminal>, <whichcoeffs> ) for rcwa mappings, (6)
##
InstallMethod( Trajectory,
               "for an rcwa mapping, coefficients (RCWA)", ReturnTrue,
               [ IsRcwaMapping, IsRingElement, IsObject, IsString ], 0,

  function ( f, n, lngterm, whichcoeffs )

    local  coeffs, triple, traj, length, terminal,
           c, m, d, pos, res, r, deg, R, q, x;

    if not IsRcwaMappingStandardRep(f) then f := StandardRep(f); fi;
    if   IsPosInt(lngterm)           then length   := lngterm;
    elif IsListOrCollection(lngterm) then terminal := lngterm;
    else TryNextMethod(); fi;
    if   not n in Source(f) or not whichcoeffs in ["AllCoeffs","LastCoeffs"]
    then TryNextMethod(); fi;
    c := Coefficients(f); m := Modulus(f);
    traj := [n mod m];
    if   IsBound(length)
    then for pos in [2..length]  do n := n^f; Add(traj,n mod m); od;
    else while not n in terminal do n := n^f; Add(traj,n mod m); od; fi;
    if IsRcwaMappingOfGFqx(f) then
      deg := DegreeOfLaurentPolynomial(m);
      R   := Source(f);
      q   := Size(CoefficientsRing(R));
      x   := IndeterminatesOfPolynomialRing(R)[1];
      res := AllGFqPolynomialsModDegree(q,deg,x);
    else res := [0..m-1]; fi;
    triple := [1,0,1] * One(Source(f)); coeffs := [triple];
    for pos in [1..Length(traj)-1] do
      r := Position(res,traj[pos]);
      triple := [ c[r][1] * triple[1],
                  c[r][1] * triple[2] + c[r][2] * triple[3],
                  c[r][3] * triple[3] ];
      triple := triple/Gcd(triple);
      if whichcoeffs = "AllCoeffs" then Add(coeffs,triple); fi;
    od;
    if whichcoeffs = "AllCoeffs" then return coeffs; else return triple; fi;
  end );

#############################################################################
##
#F  GluckTaylorInvariant( <l> ) . .  Gluck-Taylor invariant of trajectory <l>
##
InstallGlobalFunction( GluckTaylorInvariant,

  function ( l )
    if not IsList(l) or not ForAll(l,IsInt) then return fail; fi;
    return Sum([1..Length(l)],i->l[i]*l[i mod Length(l) + 1])/(l*l);
  end );

#############################################################################
##
#F  TraceTrajectoriesOfClasses( <f>, <S>, <maxlength> )
##
InstallGlobalFunction( TraceTrajectoriesOfClasses,

  function ( f, S, maxlength )

    local  l, k, starttime, timeout;

    l := [[S]]; k := 1;
    starttime := Runtime();
    timeout := GetOption("timeout",infinity,IsPosInt);
    repeat
      Add(l,Flat(List(l[k],cl->AsUnionOfFewClasses(cl^f))));
      k := k + 1;
      Info(InfoRCWA,2,"k = ",k,": ",ViewString(l[k]));
    until Length(l) >= maxlength or Runtime() - starttime >= timeout
       or l[k] in l{[1..k-1]};
    return l;
  end );

#############################################################################
##
#S  Probabilistic guesses concerning the behaviour of trajectories. /////////
##
#############################################################################

#############################################################################
##
#M  GuessedDivergence( <f> ) . . . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( GuessedDivergence,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  R, pow, m, c, M, approx, prev, facts, p, NrRes, exp, eps, prec;

    Info(InfoWarning,1,"Warning: GuessedDivergence: no particular return ",
                       "value is guaranteed.");
    if not IsRcwaMappingStandardRep(f) then f := StandardRep(f); fi;
    R := Source(f);
    prec := 10^8; eps := Float(1/prec);
    pow := f; exp := 1; approx := Float(0);
    repeat
      m := Modulus(pow); NrRes := Length(AllResidues(R,m));
      c := Coefficients(pow);
      facts := List(c,t->Float(Length(AllResidues(R,t[1]))/
                               Length(AllResidues(R,t[3]))));
      Info(InfoRCWA,4,"Factors = ",facts);
      M := TransitionMatrix(pow,m);
      p := List(TransposedMat(M),l->Float(Sum(l)/NrRes));
      Info(InfoRCWA,4,"p = ",p);
      prev := approx;
      approx := Product(List([1..NrRes],i->facts[i]^p[i]))^Float(1/exp);
      Info(InfoRCWA,2,"Approximation = ",approx);
      pow := pow * f; exp := exp + 1;
    until AbsoluteValue(approx-prev) < eps;
    return approx;
  end );

#############################################################################
##
#M  LikelyContractionCentre( <f>, <maxn>, <bound> ) .  for rcwa mappings of Z
##
InstallMethod( LikelyContractionCentre,
               "for rcwa mapping of Z and two positive integers (RCWA)",
               true, [ IsRcwaMappingOfZ, IsPosInt, IsPosInt ], 0,

  function ( f, maxn, bound )

    local  ReducedSetOfStartingValues, S0, S, n, n_i, i, seq;

    ReducedSetOfStartingValues := function ( S, f, lng )

      local  n, min, max, traj;

      min := Minimum(S); max := Maximum(S);
      for n in [min..max] do
        if n in S then
          traj := Set(Trajectory(f,n,lng){[2..lng]});
          if not n in traj then S := Difference(S,traj); fi;
        fi;
      od;
      return S;
    end;

    Info(InfoWarning,1,"Warning: `LikelyContractionCentre' is highly ",
                       "probabilistic.\nThe returned result can only be ",
                       "regarded as a rough guess.\n",
                       "See ?LikelyContractionCentre for more information.");
    if IsBijective(f) then return fail; fi;
    S := ReducedSetOfStartingValues([-maxn..maxn],f,8);
    Info(InfoRCWA,1,"#Remaining values to be examined after first ",
                    "reduction step: ",Length(S));
    S := ReducedSetOfStartingValues(S,f,64);
    Info(InfoRCWA,1,"#Remaining values to be examined after second ",
                    "reduction step: ",Length(S));
    S0 := [];
    for n in S do
      seq := []; n_i := n;
      while AbsInt(n_i) <= bound do
        if n_i in S0 then break; fi;
        if n_i in seq then
          S0 := Union(S0,Cycle(f,n_i));
          Info(InfoRCWA,1,"|S0| = ",Length(S0));
          break;
        fi;
        AddSet(seq,n_i);
        n_i := n_i^f;
        if   AbsInt(n_i) > bound
        then Info(InfoRCWA,3,"Given bound exceeded, start value ",n); fi;
      od;
      if n >= maxn then break; fi;
    od;
    return S0;
  end );

#############################################################################
##
#S  Finite cycles of an rcwa permutation. ///////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  ShortCycles( <sigma>, <S>, <maxlng> ) for bij. rcwa map., set & pos. int.
##
InstallMethod( ShortCycles,
               Concatenation("for a bijective rcwa mapping, a set and ",
                             "a positive integer (RCWA)"),
               ReturnTrue,
               [ IsRcwaMapping, IsListOrCollection, IsPosInt ], 0,

  function ( sigma, S, maxlng )

    local  cycs, absvals, minpos, i;

    if   not IsBijective(sigma) or not IsSubset(Source(sigma),S)
    then TryNextMethod(); fi;
    cycs := List(ShortOrbits(Group(sigma),S,maxlng),
                 orb->Cycle(sigma,Minimum(orb)));
    if IsRcwaMappingOfZ(sigma) then
      SortParallel(List(cycs,cyc->AbsInt(cyc[1])),cycs);
      for i in [1..Length(cycs)] do
        if not ForAll(cycs[i],IsPosInt) then
          absvals := List(cycs[i],AbsInt);
          minpos  := Position(absvals,Minimum(absvals));
          cycs[i] := Concatenation(cycs[i]{[minpos..Length(cycs[i])]},
                                   cycs[i]{[1..minpos-1]});
        fi;
      od;
    fi;
    return cycs;
  end );

#############################################################################
##
#M  ShortCycles( <sigma>, <S>, <maxlng>, <maxn> )
##
InstallMethod( ShortCycles,
               Concatenation("for a bijective rcwa mapping of Z, ",
                             "a set and two positive integers (RCWA)"),
               ReturnTrue, [ IsRcwaMappingOfZ, IsListOrCollection,
                             IsPosInt, IsPosInt ], 0,

  function ( sigma, S, maxlng, maxn )

    local  cycs, cyc, done, min, max, lng, absvals, minpos, n, m, i, j;

    if   not IsBijective(sigma) or not ForAll(S,IsInt)
    then TryNextMethod(); fi;

    min := Minimum(S); max := Maximum(S);

    cycs := [];
    done := List(S,n->false);
    while false in done do
      i := Position(done,false); done[i] := true;
      n := S[i]; m := n; cyc := []; lng := 0;
      repeat
        Add(cyc,m); m := m^sigma; lng := lng + 1;
        if m >= min and m <= max then
          j := PositionSorted(S,m);
          if j <> fail and S[j] = m then done[j] := true; fi;
        fi;
      until m = n or lng >= maxlng or AbsInt(m) > maxn;
      if m = n then Add(cycs,cyc); fi;
    od;

    SortParallel(List(cycs,cyc->AbsInt(cyc[1])),cycs);
    if min < 0 then
      for i in [1..Length(cycs)] do
        if not ForAll(cycs[i],IsPosInt) then
          absvals := List(cycs[i],AbsInt);
          minpos  := Position(absvals,Minimum(absvals));
          cycs[i] := Concatenation(cycs[i]{[minpos..Length(cycs[i])]},
                                   cycs[i]{[1..minpos-1]});
        fi;
      od;
    fi;
    return cycs;
  end );

#############################################################################
##
#M  ShortCycles( <f>, <maxlng> )  for rcwa mapping of Z or Z_(pi) & pos. int.
##
InstallMethod( ShortCycles,
               Concatenation("for an rcwa mapping of Z or Z_(pi) and ",
                             "a positive integer (RCWA)"),
               ReturnTrue, [ IsRcwaMappingOfZOrZ_pi, IsPosInt ], 0,

  function ( f, maxlng )

    local  R, cycles, cyclesbuf, cycs, cyc, fp, pow, exp,
           m, min, minshift, l, i;

    R := Source(f); cycles := []; pow := One(f);
    for exp in [1..maxlng] do
      pow  := pow * f;
      m    := Modulus(pow);
      fp   := FixedPointsOfAffinePartialMappings(pow);
      cycs := List(Filtered(TransposedMat([AllResidueClassesModulo(R,m),fp]),
                            s->IsSubset(s[1],s[2]) and not IsEmpty(s[2])),
                   t->t[2]);
      cycs := List(cycs,ShallowCopy);
      for cyc in cycs do
        for i in [1..exp-1] do Add(cyc,cyc[i]^f); od;
      od;
      cycles := Concatenation(cycles,cycs);
    od;
    cycles := Filtered(cycles,cyc->Length(Set(cyc))=Length(cyc));
    cyclesbuf := ShallowCopy(cycles); cycles := [];
    for i in [1..Length(cyclesbuf)] do
      if not Set(cyclesbuf[i]) in List(cyclesbuf{[1..i-1]},AsSet) then
        cyc := cyclesbuf[i]; l := Length(cyc);
        min := Minimum(cyc); minshift := l - Position(cyc,min) + 1;
        cyc := Permuted(cyc,SortingPerm(Concatenation([2..l],[1]))^minshift);
        Add(cycles,cyc);
      fi;
    od;
    return cycles;
  end );

#############################################################################
##
#M  CycleRepresentativesAndLengths( <g>, <S> ) . . . . . . . . default method
##
InstallMethod( CycleRepresentativesAndLengths,
               "default method (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsListOrCollection ], 0,

  function ( g, S )

    local  replng, rem, cyc, rep, n, i, j;

    replng := [];
    rem    := List(S,n->n^g<>n);
    for i in [1..Length(S)] do
      if rem[i] = false then continue; fi;
      rep := S[i];
      cyc := ComputeCycleLength(g,rep:small:=S);
      if not cyc.aborted then Add(replng,[rep,cyc.length]);
                         else Add(replng,[rep,fail]); fi;
      for n in cyc.smallpoints do rem[PositionSorted(S,n)] := false; od;
    od;
    return replng;
  end );

#############################################################################
##
#F  ComputeCycleLength( <g>, <n> )
##
InstallGlobalFunction( ComputeCycleLength,

  function ( g, n0 )

    local  n, steps, max, maxpos, smallpoints, result,
           notify, small, abortat, aborted, quiet;

    n := n0; steps := 0; max := n; maxpos := 1; smallpoints := [n0];
    notify  := ValueOption("notify");
    small   := ValueOption("small");
    abortat := ValueOption("abortat");
    quiet   := ValueOption("quiet") = true;
    if   not IsPosInt(notify) and not notify in [0,infinity]
    then notify := 10000; fi;
    aborted := false;
    repeat
      n := n^g;
      steps := steps + 1;
      if n > max then
        max    := n;
        maxpos := steps;
      fi;
      if IsList(small) and n in small then Add(smallpoints,n); fi;
      if not quiet and not notify in [0,infinity]
        and steps mod notify = 0
      then
        Print("n = ",n0,": after ",steps," steps, the iterate has ",
              LogInt(AbsInt(n),2)+1," binary digits.\n");
      fi;
      if IsPosInt(abortat)
        and (steps >= abortat or (abortat >= 10^20 and n > abortat))
      then
        aborted := true; break;
      fi; 
    until n = n0;
    result := rec( g       := g,
                   n       := n0,
                   length  := steps,
                   maximum := max,
                   maxpos  := maxpos,
                   aborted := aborted );
    if IsList(small) then result.smallpoints := Set(smallpoints); fi;
    return result;
  end );

#############################################################################
##
#M  ShortResidueClassCycles( <g>, <modbound>, <maxlng> )
##
##  Probably now obsolete; superseded by method below.
##
InstallMethod( ShortResidueClassCycles,
               "for an rcwa permutation of Z and 2 positive integers (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZ, IsPosInt, IsPosInt ], 0,

  function ( g, modbound, maxlng )

    local  cycles, cycle, cycs, lngs, lng, startpts, cycbound,
           cl, S, affsrc, divs, c, m, r; 

    if not IsRcwaMappingStandardRep(g) then g := StandardRep(g); fi;

    affsrc := LargestSourcesOfAffineMappings(g);
    divs := Difference(DivisorsInt(modbound),[1]);

    S := Intersection([0..modbound-1],Support(g));
    cycbound := ValueOption("cycbound");
    if   cycbound = fail
    then Info(InfoRCWA,2,"ShortResidueClassCycles: option cycbound not set");
         cycs := ShortCycles(g,S,maxlng);
    else cycs := ShortCycles(g,S,maxlng,cycbound); fi;
    lngs := Set(List(cycs,Length));

    cycles := List(AsUnionOfFewClasses(Difference(Integers,Support(g))),
                   cl->[cl]);

    for lng in lngs do
      Info(InfoRCWA,2,"ShortResidueClassCycles: checking cycle length ",lng);
      startpts := List(Filtered(cycs,cyc->Length(cyc)=lng),l->l[1]);
      for m in divs do
        for r in Filtered(startpts,s->s<m) do
          if IsSubset(startpts,[r,r+m..modbound-m+r]) and
             not ForAny(cycles,
                        cyc->ForAny(cyc,cl->(r-cl!.r[1]) mod Gcd(m,cl!.m)=0)) 
          then
            cycle := []; cl := ResidueClass(r,m);
            if  m mod Mod(g) <> 0
              and Number(affsrc,src->Intersection(src,cl)<>[]) > 1
            then continue; fi;
            repeat
              Add(cycle,cl);
              if cl!.m mod g!.modulus <> 0 then cl := cl^g; else
                c := g!.coeffs[cl!.r[1] mod g!.modulus + 1];
                cl := ResidueClassUnionNC(Integers,cl!.m*c[1]/c[3],
                                          [(cl!.r[1]*c[1]+c[2])/c[3]]);
              fi;
            until not IsResidueClass(cl) or cl = cycle[1]
                  or Length(cycle) > maxlng;
            if cl = cycle[1] then
              Add(cycles,cycle);
            fi;
          fi;
        od;
      od;
    od;

    return cycles;
  end );

#############################################################################
##
#M  ShortResidueClassCycles( <g>, <modbound>, <maxlng> )
##
InstallMethod( ShortResidueClassCycles,
               "for an rcwa permutation of Z and 2 positive integers (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZ, IsPosInt, IsPosInt ], 5,

  function ( g, modbound, maxlng )

    local  cycles, orbits;

    orbits := ShortResidueClassOrbits(Group(g),modbound,maxlng);
    cycles := Set(List(orbits,orb->Cycle(g,orb[1])));
    return cycles;
  end );

#############################################################################
##
#M  ResidueClassCyclesThroughResidueClass( <g>, <cl>, <modulusbound> )
##
InstallMethod( ResidueClassCyclesThroughResidueClass,
               Concatenation("for an rcwa permutation of Z, a residue class",
                             " and a positive integer (RCWA)"),
               ReturnTrue, [ IsRcwaMappingOfZ, IsResidueClass, IsPosInt ], 0,

  function ( g, cl, maxmod )

    local  Try, cycs, cyc, cls;

    Try := function ( cl0 )

      local  cyc, cl, cls;

      cl  := cl0;
      cyc := [];
      repeat
        Add(cyc,cl);
        cl := cl^g;
      until cl = cl0 or not IsResidueClass(cl);
      if cl = cl0 then
        Add(cycs,cyc);
      else
        cls := SplittedClass(cl0,Length(AsUnionOfFewClasses(cl)));
        if Modulus(cls[1]) <= maxmod then
          Perform(cls,Try);
        fi;
      fi;
    end; 

    g  := SparseRep(g);
    cl := SparseRep(cl);

    cls := Union(List(LargestSourcesOfAffineMappings(g),
                      AsUnionOfFewClasses));
    if not IsBijective(g)
       or Number(cls,cl2->Intersection(cl,cl2)<>[]) > 1
    then
      return fail;
    fi;

    cycs := [];
    Try( cl );
    SortParallel(List(cycs,cyc->[Length(cyc),
                                 Modulus(cyc[1]),Residue(cyc[1])]),cycs);

    return cycs;
  end );

#############################################################################
##
#M  DrawResidueClassCyclesThroughResidueClassPicture
#M    ( <g>, <cl>, <modulusbound>, <edge>, <filename> )
##
InstallMethod( DrawResidueClassCyclesThroughResidueClassPicture,
               Concatenation("for an rcwa permutation of Z, a residue class",
                             ", two positive integers and a string (RCWA)"),
               ReturnTrue, [ IsRcwaMappingOfZ, IsResidueClass, IsPosInt,
                             IsPosInt, IsString ], 0,

  function ( g, cl, modulusbound, edge, filename )

    local  classcycles, repslngs, lngset, lngcolor, color, splitfactor,
           img, rect, w, h, x, y, r, m, lng, pos, i, j;

    img := Concatenation(
             """<?xml version="1.0" encoding="UTF-8" standalone="no"?> """,
             """<!DOCTYPE svg PUBLIC "-//W3C//DTD SVG 1.1//EN" """,
             """ "http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd"> """,
             """<svg xmlns="http://www.w3.org/2000/svg" """,
             """xmlns:xlink="http://www.w3.org/1999/xlink" version="1.1" """,
             """width="edgewidth" height="edgeheight">""",
             """<desc>Residue class partition</desc>""");
    rect := Concatenation("  <rect fill=\"#000000\" width=\"","edgewidth",
                          "\" height=\"","edgeheight",
                          "\" transform=\"translate(",
                          String(0),",",String(0),")\"/>\n");
    img := Concatenation(img,rect);

    color := ["#ffff44","#0000ff","#00ff00","#ff0000","#ffff00","#ff00ff",
              "#00ffff","#8800ff","#00ff88","#ffaabb","#66ff00","#7788ff",
              "#ee44ff","#bb88ff","#ff0044","#fff070","#ffff66","#44ff99",
              "#aabbff","#00aaff","#77ff22","#ff66aa","#eeff88","#33ff66",
              "#aa55bb","#5500ff","#66ff77","#ff7777","#77ff77","#6644ff"];

    classcycles := ResidueClassCyclesThroughResidueClass(g,cl,modulusbound);
    r           := Residue(cl);
    m           := Modulus(cl);
    repslngs    := List(classcycles,cyc->[(cyc[1]-r)/m,Length(cyc)]);
    lngset      := Set(repslngs,l->l[2]);

    splitfactor := Set(QuotientsList(Set(repslngs,l->Modulus(l[1]))));
    if Length(splitfactor) = 1 then
      splitfactor := splitfactor[1];
    else
      Error("sorry, this case is presently not supported");
      return fail;
    fi;

    img := Concatenation(ReplacedString(img,"edgeheight",String(edge)),"\n");
    img := ReplacedString(img,"edgewidth",String(splitfactor^0.5 * edge));

    lngcolor := [];
    pos      := 1;
    for lng in lngset do
      if pos <= Length(color) then
        lngcolor[lng] := color[pos];
      else
        lngcolor[lng] := Concatenation("#",
                           HexStringInt(2^24+Random([0..2^24-1])){[2..7]});
      fi;
      pos := pos + 1;
    od;

    for i in [1..Length(repslngs)] do
      r   := Residue(repslngs[i][1]);
      m   := Modulus(repslngs[i][1]);
      lng := repslngs[i][2];
      w   := splitfactor^0.5 * edge;
      h   := edge;
      x   := 0;
      y   := 0;
      for j in [1..LogInt(m,splitfactor)] do
        if j mod 2 = 0 then
          h := h/splitfactor;
          y := y + h * (r mod splitfactor);
        else
          w := w/3;
          x := x + w * (r mod splitfactor);
        fi;
        r := Int(r/splitfactor);
      od;
      rect := Concatenation("  <rect fill=\"",lngcolor[lng],
                            "\" width=\"",String(w),
                            "\" height=\"",String(h),
                            "\" transform=\"translate(",
                            String(x),",",String(y),")\"/>\n");
      img := Concatenation(img,rect);
    od;
    img := Concatenation(img,"</svg>\n\n");

    if PositionSublist(filename,".svg") = fail then
      Append(filename,".svg");
    fi;
    if Positions(filename,'/') = [] then
      FileString(Concatenation("/user/GAP/pictures/",filename),img);
    else
      FileString(filename,img);
    fi;
  end );

#############################################################################
##
#M  FixedResidueClasses( <g>, <maxmod> )
##
InstallMethod( FixedResidueClasses,
               "for an rcwa mapping of Z and a positive integer (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZ, IsPosInt ], 0,

  function ( g, maxmod )

    local  cls, fixed, cl, r, m;

    cls := Concatenation(List([2..maxmod],
                              m->AllResidueClassesModulo(Integers,m)));
    fixed := [];
    for cl in cls do
      r := Residue(cl); m := Modulus(cl);
      if ForAny([r,r+m..r+15*m],n->n^g mod m <> r) then continue; fi;
      if cl^g = cl then Add(fixed,cl); fi;
    od;
    return fixed;
  end );

#############################################################################
##
#S  Restriction monomorphisms and induction epimorphisms. ///////////////////
##
#############################################################################

#############################################################################
##
#M  Restriction( <g>, <f> ) . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( Restriction, "for rcwa mappings (RCWA)", IsIdenticalObj,
               [ IsRcwaMapping, IsRcwaMapping ], 0,

  function ( g, f )

    local  gf;

    if not IsInjective(f) then return fail; fi;

    gf := RestrictedPerm( RightInverse(f) * g * f, Image(f) );

    Assert(4,g*f=f*gf,"Restriction: Diagram does not commute.\n");

    if HasIsInjective(g)  then SetIsInjective(gf,IsInjective(g)); fi;
    if HasIsSurjective(g) then SetIsSurjective(gf,IsSurjective(g)); fi;
    if HasIsTame(g)       then SetIsTame(gf,IsTame(g)); fi;
    if HasOrder(g)        then SetOrder(gf,Order(g)); fi;

    return gf;
  end );

#############################################################################
##
#M  Induction( <g>, <f> ) . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( Induction, "for rcwa mappings (RCWA)", IsIdenticalObj,
               [ IsRcwaMapping, IsRcwaMapping ], 0,

  function ( g, f )

    local  gf;

    if    not IsInjective(f) or not IsSubset(Image(f),MovedPoints(g))
       or not IsSubset(Image(f),MovedPoints(g)^g) then return fail; fi;

    gf := f * g * RightInverse(f);

    Assert(4,gf*f=f*g,"Induction: Diagram does not commute.\n");

    if HasIsInjective(g)  then SetIsInjective(gf,IsInjective(g)); fi;
    if HasIsSurjective(g) then SetIsSurjective(gf,IsSurjective(g)); fi;
    if HasIsTame(g)       then SetIsTame(gf,IsTame(g)); fi;
    if HasOrder(g)        then SetOrder(gf,Order(g)); fi;

    return gf;
  end );

#############################################################################
##
#S  Extracting roots of rcwa permutations. //////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  Root( <sigma>, <k> ) . . . . . .  for an element of CT(Z) of finite order
##
InstallMethod( Root,
               "for an element of CT(Z) of finite order (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZ, IsPosInt ], 10,

  function ( sigma, k )

    local  root, regroot, k_reg, k_sing, order, P, remaining, cycle, l, i, j;

    if k = 1 then return sigma; fi;
    if not IsClassWiseOrderPreserving(sigma) or not IsTame(sigma)
      or Order(sigma) = infinity
      or not ForAll(Factorization(sigma),IsClassTransposition)
    then TryNextMethod(); fi;
    order     := Order(sigma);
    k_sing    := Product(Filtered(Factors(k),p->order mod p = 0));
    k_reg     := k/k_sing;
    regroot   := sigma^(1/k_reg mod order); 
    if k_sing = 1 then return regroot; fi;
    P         := RespectedPartition(regroot);
    remaining := ShallowCopy(P);
    root      := One(sigma);
    repeat
      cycle     := Cycle(regroot,remaining[1]);
      l         := Length(cycle);
      remaining := Difference(remaining,cycle);
      cycle     := List(cycle,cl->SplittedClass(cl,k_sing));
      for i in [1..l] do
        for j in [1..k_sing] do
          if [i,j] <> [1,1] then
            root := root * ClassTransposition(cycle[1][1],cycle[i][j]);
          fi;
        od;
      od;
    until IsEmpty(remaining);
    return root;    
  end );

#############################################################################
##
#M  Root( <sigma>, <k> ) . . .  for a cwop. rcwa mapping of Z of finite order
##
InstallMethod( Root,
               "for a cwop. rcwa mapping of Z of finite order (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZ, IsPosInt ], 0,

  function ( sigma, k )

    local  root, g, x;

    if k = 1 then return sigma; fi;
    if IsOne(sigma) then
      root := Product([1..k-1],r->ClassTransposition(0,k,r,k));
      SetOrder(root,k); return root;
    fi;
    if not IsClassWiseOrderPreserving(sigma) or not IsTame(sigma)
      or Order(sigma) = infinity
    then TryNextMethod(); fi;
    g    := Product(Filtered(Factorization(sigma),IsClassTransposition));
    x    := RepresentativeAction(RCWA(Integers),g,sigma);
    root := Root(g,k)^x;
    return root;
  end );

#############################################################################
##
#S  Factoring an rcwa permutation into class shifts, ////////////////////////
#S  class reflections and class transpositions. /////////////////////////////
##
#############################################################################

#############################################################################
##
#M  CTCSCRSplit( <g> ) . . . . . . . . . . . . . . for rcwa permutations of Z
##
InstallMethod( CTCSCRSplit,
               "for bijective rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ ], 0,

  function ( g )

    local  coeffs, rev, reverts, revert, shifts, shift,
           cl, img, c, r, m, e, stdrep, listfactors;

    if not IsBijective(g) then TryNextMethod(); fi;
    listfactors := ValueOption("ListFactors");
    stdrep := IsRcwaMappingOfZInStandardRep(g);
    g := SparseRep(g);
    if not IsClassWiseOrderPreserving(g) then
       rev     := ClassWiseOrderReversingOn(g);
       reverts := List(AsUnionOfFewClasses(rev^g),
                       cl->SparseRep(ClassReflection(cl)));
       revert  := Product(reverts);
       g := g * revert^-1;
    else reverts := []; revert := One(g); fi;
    shifts := [];
    coeffs := Coefficients(g);
    for c in coeffs do
      cl  := ResidueClassWithFixedRep(c[2],c[1]);
      img := Classes(cl^g)[1];
      m := img[1]; r := img[2];
      e := (r - r mod m)/m;
      if e <> 0 then Add(shifts,SparseRep(ClassShift(r,m)^e)); fi;
    od;
    if shifts <> [] then
      shift := Product(shifts);
    else
      shift := One(g);
    fi;
    g := g * shift^-1;
    if stdrep then
      g      := StandardRep(g);
      shift  := StandardRep(shift);
      revert := StandardRep(revert);
      if listfactors = true then
        reverts := List(reverts,StandardRep);
        shifts  := List(shifts,StandardRep);
      fi;
    fi;
    if listfactors <> true then
      return [ g, shift, revert ];
    else
      return [ g, shifts, reverts ];
    fi;
  end );

#############################################################################
##
#M  FactorizationIntoCSCRCT( <g> ) . . . . . for bijective rcwa mappings of Z
##
InstallMethod( FactorizationIntoCSCRCT,
               "for bijective rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ ], 0,

  function ( g )

    local  DivideBy, SaveState, RevertDirectionAndJumpBack, StateInfo,
           facts, gbuf, leftfacts, leftfactsbuf, rightfacts, rightfactsbuf,
           elm, direction, sgn, log, loop, rev, revert, affsrc, P, oldP,
           newP, parts, block, h, cycs, cyc, gfixP, cl, rest, c, m, r,
           multfacts, divfacts, p, q, Smult, Sdiv, clSmult, clSdiv,
           pairs, pair, diffs, largeprimes, splitpair, splittedpairs,
           splittedpair, d, dpos, disjoint, ctchunk,
           multswitches, divswitches, kmult, kdiv, i, j, k;

    StateInfo := function ( )
      Info(InfoRCWA,1,"Modulus(<g>) = ",Modulus(g),
                      ", Multiplier(<g>) = ",Multiplier(g),
                      ", Divisor(<g>) = ",Divisor(g));
      Info(InfoRCWA,2,"MappedPartitions(<g>) = ",MappedPartitions(g));
    end;

    SaveState := function ( )
      gbuf          := g;
      leftfactsbuf  := ShallowCopy(leftfacts);
      rightfactsbuf := ShallowCopy(rightfacts);
    end;

    RevertDirectionAndJumpBack := function ( )
      if   direction  = "from the right"
      then direction := "from the left";
      else direction := "from the right"; fi;
      Info(InfoRCWA,1,"Jumping back and retrying with divisions ",
                      direction,".");
      g := gbuf; leftfacts := leftfactsbuf; rightfacts := rightfactsbuf;
      k[Maximum(p,q)] := k[Maximum(p,q)] + 1;
    end;

    DivideBy := function ( l )

      local  fact, prod, areCTs;

      areCTs := ValueOption("ct") = true;
      if not IsList(l) then l := [l]; fi;
      for fact in l do # Factors in divisors list must commute.
        Info(InfoRCWA,1,"Dividing by ",ViewString(fact)," ",direction,".");
      od;
      if direction = "from the right" then
        if   areCTs
        then prod   := Product(l);
        else prod   := Product(Reversed(l))^-1; fi;
        g           := g * prod;
        rightfacts  := Concatenation(Reversed(l),rightfacts);
      else
        if   areCTs
        then prod   := Product(Reversed(l));
        else prod   := Product(l)^-1; fi;
        g           := prod * g;
        leftfacts   := Concatenation(leftfacts,l);
      fi;
      StateInfo();
      Assert(4,IsBijective(RcwaMapping(ShallowCopy(Coefficients(g)))));
    end;

    if not IsBijective(g) then return fail; fi;
    if IsOne(g) then return [g]; fi;

    if not IsRcwaMappingStandardRep(g) then g := StandardRep(g); fi;

    leftfacts := []; rightfacts := []; facts := []; elm := g;
    direction := ValueOption("Direction");
    if direction <> "from the left" then direction := "from the right"; fi;
    multswitches := []; divswitches := []; log := []; loop := false;

    if not IsClassWiseOrderPreserving(g) then

      Info(InfoRCWA,1,"Making the mapping class-wise order-preserving.");

      rev    := ClassWiseOrderReversingOn(g);
      revert := [List(AsUnionOfFewClasses(rev  ),ClassReflection),
                 List(AsUnionOfFewClasses(rev^g),ClassReflection)];
      if   Length(revert[1]) <= Length(revert[2])
      then g := Product(revert[1])^-1 * g;
      else g := g * Product(revert[2])^-1; fi;

    else revert := [[],[]]; fi;

    if IsIntegral(g) then

      Info(InfoRCWA,1,"Determining largest sources of affine mappings.");

      affsrc := Union(List(LargestSourcesOfAffineMappings(g),
                           AsUnionOfFewClasses));
      m := Modulus(g);

      Info(InfoRCWA,1,"Computing respected partition.");

      if ValueOption("ShortenPartition") <> false then
        h := PermList(List([0..m-1],i->i^g mod m + 1));
        P := Set(List(affsrc,S->Intersection(S,[0..m-1]))) + 1;
        repeat
          oldP := ShallowCopy(P); newP := [];
          P    := List(P,block->OnSets(block,h));
          for i in [1..Length(P)] do
            if P[i] in oldP then Add(newP,P[i]); else # split
              parts := List([1..Length(oldP)],j->Intersection(P[i],oldP[j]));
              parts := Filtered(parts,block->not IsEmpty(block));
              newP  := Concatenation(newP,parts);
            fi;
          od;
          P := Set(newP);
        until P = oldP;
        P := Set(P,res->ResidueClassUnion(Integers,m,res-1));
        Assert(4,Union(P)=Integers);
        if   not ForAll(P,IsResidueClass)
        then P := AllResidueClassesModulo(Modulus(g)); fi;
      else P := AllResidueClassesModulo(Modulus(g)); fi;

      if InfoLevel(InfoRCWA) >= 1 then
        Print("#I  Computing induced permutation on respected partition ");
        View(P); Print(".\n");
      fi;

      if   ValueOption("ShortenPartition") <> false
      then h := PermutationOpNC(g,P,OnPoints);
      else h := PermList(List([0..Modulus(g)-1],i->i^g mod Modulus(g) + 1));
      fi;
      cycs := Orbits(Group(h),MovedPoints(h));
      cycs := List(cycs,cyc->Cycle(h,Minimum(cyc)));
      for cyc in cycs do
        for i in [2..Length(cyc)] do
          Add(facts,ClassTransposition(P[cyc[1]],P[cyc[i]]));
        od;
      od;

      Info(InfoRCWA,1,"Factoring the rest into class shifts.");

      gfixP := g/Product(facts); # gfixP stabilizes the partition P.
      for cl in P do
        rest := RestrictedPerm(gfixP,cl);
        if IsOne(rest) then continue; fi;
        m := Modulus(rest); r := Residue(cl);
        c := Coefficients(rest)[r+1];
        facts := Concatenation([ClassShift(r,m)^(c[2]/m)],facts);
      od;

    else

      StateInfo();

      repeat

        k := ListWithIdenticalEntries(Maximum(Union(Factors(Multiplier(g)),
                                                    Factors(Divisor(g)))),1);
        while not IsBalanced(g) do

          p := 1; q := 1;
          multfacts := Set(Factors(Multiplier(g)));
          divfacts  := Set(Factors(Divisor(g)));
          if   not IsSubset(divfacts,multfacts)
          then p := Maximum(Difference(multfacts,divfacts)); fi;
          if   not IsSubset(multfacts,divfacts)
          then q := Maximum(Difference(divfacts,multfacts)); fi;

          if   Maximum(p,q) < Maximum(Union(multfacts,divfacts))
          then break; fi;

          if Maximum(p,q) >= 3 then
            if p > q then # Additional prime p in multiplier.
              if p in multswitches then RevertDirectionAndJumpBack(); fi;
              Add(divswitches,p); SaveState();
              DivideBy(PrimeSwitch(p,k[p]));
            else          # Additional prime q in divisor.
              if q in divswitches then RevertDirectionAndJumpBack(); fi;
              Add(multswitches,q); SaveState();
              DivideBy(PrimeSwitch(q,k[q])^-1);
            fi;
          elif 2 in [p,q]
          then DivideBy(ClassTransposition(0,2,1,4):ct); fi;

        od;

        if IsOne(g) then break; fi;

        p     := Maximum(Factors(Multiplier(g)*Divisor(g)));
        kmult := Number(Factors(Multiplier(g)),q->q=p);
        kdiv  := Number(Factors(Divisor(g)),q->q=p);
        k     := Maximum(kmult,kdiv);
        Smult := Multpk(g,p,kmult);
        Sdiv  := Multpk(g,p,-kdiv);
        if   direction = "from the right"
        then Smult := Smult^g; Sdiv := Sdiv^g; fi;

        Info(InfoRCWA,1,"p = ",p,", kmult = ",kmult,", kdiv = ",kdiv);

        # Search residue classes r1(m1) in Smult, r2(m2) in Sdiv
        # with m1/m2 = p^k.

        clSmult := AsUnionOfFewClasses(Smult);
        clSdiv  := AsUnionOfFewClasses(Sdiv);

        if InfoLevel(InfoRCWA) >= 1 then
          if   direction = "from the right"
          then Print("#I  Images of c"); else Print("#I  C"); fi;
          Print("lasses being multiplied by q*p^kmult:\n#I  ");
          ViewObj(clSmult);
          if   direction = "from the right"
          then Print("\n#I  Images of c"); else Print("\n#I  C"); fi;
          Print("lasses being divided by q*p^kdiv:\n#I  ");
          ViewObj(clSdiv); Print("\n");
        fi;

        if not [p,kmult,kdiv,clSmult,clSdiv,direction] in log then

          Add(log,[p,kmult,kdiv,clSmult,clSdiv,direction]);

          repeat
            if   direction = "from the right"
            then sgn := 1; else sgn := -1; fi;
            pairs := Filtered(Cartesian(clSmult,clSdiv),
                     pair->PadicValuation(Mod(pair[1])/Mod(pair[2]),p)
                           = sgn * k);
            pairs := Set(pairs);
            if pairs = [] then
              diffs := List(Cartesian(clSmult,clSdiv),
                       pair->PadicValuation(Mod(pair[1])/Mod(pair[2]),p));
              if Maximum(diffs) < sgn * k then
                Info(InfoRCWA,2,"Splitting classes being multiplied by ",
                                "q*p^kmult.");
                clSmult := Flat(List(clSmult,cl->SplittedClass(cl,p)));
              fi;
              if Maximum(diffs) > sgn * k then
                Info(InfoRCWA,2,"Splitting classes being divided by ",
                                "q*p^kdiv.");
                clSdiv := Flat(List(clSdiv,cl->SplittedClass(cl,p)));
              fi;
            fi;
          until pairs <> [];

          Info(InfoRCWA,1,"Found ",Length(pairs)," pairs.");

          splittedpairs := [];
          for i in [1..Length(pairs)] do
            largeprimes := List(pairs[i],
                                cl->Filtered(Factors(Modulus(cl)),q->q>p));
            largeprimes := List(largeprimes,Product);
            splitpair   := largeprimes/Gcd(largeprimes);
            if 1 in splitpair then # Omit non-disjoint split.
              if splitpair = [1,1] then Add(splittedpairs,pairs[i]); else
                d := Maximum(splitpair); dpos := 3-Position(splitpair,d);
                if dpos = 1 then
                  splittedpair := List(SplittedClass(pairs[i][1],d),
                                       cl->[cl,pairs[i][2]]);
                else
                  splittedpair := List(SplittedClass(pairs[i][2],d),
                                       cl->[pairs[i][1],cl]);
                fi;
                splittedpairs := Concatenation(splittedpairs,splittedpair);
              fi;
            fi;
          od;

          pairs := splittedpairs;
          Info(InfoRCWA,1,"After filtering and splitting: ",
                          Length(pairs)," pairs.");

          repeat
            disjoint := [pairs[1]]; i := 1;
            while i < Length(pairs)
                  and Sum(List(Flat(disjoint),Density))
                    = Density(Union(Flat(disjoint)))
            do
              i := i + 1;
              Add(disjoint,pairs[i]); 
            od;
            if   Sum(List(Flat(disjoint),Density))
               > Density(Union(Flat(disjoint)))
            then disjoint := disjoint{[1..Length(disjoint)-1]}; fi;
            DivideBy(List(disjoint,ClassTransposition):ct);
            pairs := Difference(pairs,disjoint);
          until pairs = [];

        else
          if ValueOption("Slave") = true then
            Info(InfoRCWA,1,"A loop has been detected. Attempt failed.");
            return fail;
          else
            Info(InfoRCWA,1,"A loop has been detected. Trying to ",
                            "factor the inverse instead.");
            facts := FactorizationIntoCSCRCT(elm^-1:Slave);
            if facts = fail then
              Info(InfoRCWA,1,"Factorization of the inverse failed also. ",
                              "Giving up.");
              return fail;
            else return Reversed(List(facts,Inverse)); fi;
          fi;
        fi;

      until IsIntegral(g);

      facts := Concatenation(leftfacts,
                             FactorizationIntoCSCRCT(g:Slave),
                             rightfacts);

      if ValueOption("ExpandPrimeSwitches") = true then
        facts := Flat(List(facts,FactorizationIntoCSCRCT));
      fi;

    fi;

    if   Length(revert[1]) <= Length(revert[2])
    then facts := Concatenation(revert[1],facts);
    else facts := Concatenation(facts,revert[2]); fi;

    facts := Filtered(facts,fact->not IsOne(fact));

    if ValueOption("Slave") <> true and ValueOption("NC") <> true then
      Info(InfoRCWA,1,"Checking the result.");
      if   Product(facts) <> elm
      then Error("FactorizationIntoCSCRCT: Internal error!"); fi;
    fi;

    return facts;

  end );

#############################################################################
##
#M  FactorizationIntoCSCRCT( <g> ) . . . . . . . . . for the identity mapping
##
InstallMethod( FactorizationIntoCSCRCT,
               "for the identity mapping (RCWA)",
               true, [ IsRcwaMapping and IsOne ], 0, one -> [ one ] );

#############################################################################
##
#M  Factorization( <g> ) . . . for bijective rcwa mappings, into cs / cr / ct
##
InstallMethod( Factorization,
               "into class shifts / reflections / transpositions (RCWA)",
               true, [ IsRcwaMapping ], 0, FactorizationIntoCSCRCT );

#############################################################################
##
#F  ReducingConjugatorCT3Z( <tau> )
##
BindGlobal( "ReducingConjugatorCT3Z",

  function ( tau )

    local  w, ct, cls, cls4, cls6, cl, cl1, cl2, cl3, cl4;

    w    := [];
    cls  := Union(List([2,3,4,6,8,9,12,18],AllResidueClassesModulo));
    cls4 := AllResidueClassesModulo(4);
    cls6 := AllResidueClassesModulo(6);

    repeat

      repeat

        cl := First(cls4,cl->IsSubset(cl,Support(tau)));
        if cl = fail then break; fi;

        ct := ClassTransposition((Residue(cl)+1) mod 2,2,Residue(cl),4);
        tau := tau^ct;
        Add(w,ct); 

      until cl = fail;

      repeat

        cl := First(cls6,cl->IsSubset(cl,Support(tau)));
        if cl = fail then break; fi;

        ct := ClassTransposition((Residue(cl)+1) mod 2,2,Residue(cl),6);
        tau := tau^ct;
        Add(w,ct); 

      until cl = fail;

      cl1 := TransposedClasses(tau)[1]; cl2 := TransposedClasses(tau)[2];

      cl3 := First(cls,cl->Intersection(cl,Support(tau)) = []);

      if cl3 = fail then break; fi;

      cl4 := First(cls,cl->Intersection(cl,cl1) = []
                       and Intersection(cl,cl3) = []
                       and IsSubset(cl,cl2) and Modulus(cl) > Modulus(cl3));

      if cl4 = fail then break; fi;

      ct  := ClassTransposition(cl3,cl4);
      tau := tau^ct;
      Add(w,ct);
    
    until cl4 = fail;

    return [ tau, w ];
  end );

#############################################################################
##
#M  FactorizationIntoElementaryCSCRCT( <g> )
##
InstallMethod( FactorizationIntoElementaryCSCRCT,
               "for elements of CT_{3}(Z) (RCWA)", true,
               [ IsRcwaMappingOfZ ], 0,

  function ( g )

    local  CT3Zgens, facts, elementaryfacts, ct, ct1,
           elems, elemsold, t;

    if not IsBijective(g) then
      Error("usage: FactorizationIntoElementaryCSCRCT( <g> ), ",
            "where <g> is an rcwa permutation\n");
    fi;

    if   not IsSubset([2,3],PrimeSet(g)) or not IsSignPreserving(g)
    then TryNextMethod(); fi;

    CT3Zgens := List([ [0,2,1,2], [1,2,2,4], [0,2,1,4], [1,4,2,4],
                       [0,3,1,3], [1,3,2,3], [0,3,1,9], [0,3,4,9],
                       [0,3,7,9], [0,2,1,6], [0,3,1,6] ],
                     ClassTransposition);

    facts           := Flat(List(Factorization(g),Factorization));
    elementaryfacts := [];

    for ct in facts do
      elems := [ct];
      while not ForAll(elems,
                       ct->IsSubset([2,3,4,6,8,9],
                                    List(TransposedClasses(ct),Modulus))) do
        elemsold := ShallowCopy(elems);
        elems    := [];
        for ct1 in elemsold do
          t := ReducingConjugatorCT3Z(ct1);
          Append(elems,Concatenation(t[2],[t[1]],Reversed(t[2])));
        od;
      od;
      if   Product(elems) <> ct
      then Error("ElementaryFactorization: internal error!\n"); fi;
      Append(elementaryfacts,elems);
    od;

    return elementaryfacts;
  end );

#############################################################################
##
#E  rcwamap.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
