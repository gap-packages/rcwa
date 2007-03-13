#############################################################################
##
#W  rcwamap.gi                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains implementations of methods and functions for computing
##  with rcwa mappings of
##
##    - the ring Z of the integers, of
##    - the semilocalizations Z_(pi) of the ring of integers, and of
##    - the polynomial rings GF(q)[x] in one variable over a finite field.
##
##  See the definitions given in the file rcwamap.gd.
##
Revision.rcwamap_gi :=
  "@(#)$Id$";

#############################################################################
##
#F  RCWAInfo . . . . . . . . . . . . . . . . . . set info level of `InfoRCWA'
##
InstallGlobalFunction( RCWAInfo,
                       function ( n ) SetInfoLevel( InfoRCWA, n ); end );

#############################################################################
##
#S  Implications between the categories of rcwa mappings. ///////////////////
##
#############################################################################

InstallTrueMethod( IsMapping,     IsRcwaMapping );
InstallTrueMethod( IsRcwaMapping, IsRcwaMappingOfZOrZ_pi );
InstallTrueMethod( IsRcwaMappingOfZOrZ_pi, IsRcwaMappingOfZ );
InstallTrueMethod( IsRcwaMappingOfZOrZ_pi, IsRcwaMappingOfZ_pi );
InstallTrueMethod( IsRcwaMapping, IsRcwaMappingOfGFqx );

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
BindGlobal( "IsRcwaMappingOfGFqxInStandardRep",
             IsRcwaMappingOfGFqx and IsRcwaMappingStandardRep );

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

## Internal variables storing the rcwa mapping families used in the
## current GAP session.

BindGlobal( "Z_PI_RCWAMAPPING_FAMILIES", [] );
BindGlobal( "GFQX_RCWAMAPPING_FAMILIES", [] );

#############################################################################
##
#F  RcwaMappingsOfZ_piFamily( <R> )
##
##  The family of all rcwa mappings of a given semilocalization <R> of the
##  ring of integers.
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
##  The family of all rcwa mappings of a given polynomial ring <R> in one
##  variable over a finite field.
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
    elif IsZ_pi( R )     then return RcwaMappingsOfZ_piFamily( R );
    elif IsUnivariatePolynomialRing( R ) and IsFiniteFieldPolynomialRing( R )
    then return RcwaMappingsOfGFqxFamily( R );
    else Error("Sorry, rcwa mappings over ",R," are not yet implemented.\n");
    fi;
  end );

#############################################################################
##
#S  The methods for the general-purpose constructor for rcwa mappings. //////
##
#############################################################################

#############################################################################
##
#F  RcwaMapping( <R>, <modulus>, <coeffs> ) . . . .  method (a) in the manual
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
#F  RcwaMappingNC( <R>, <modulus>, <coeffs> ) . . NC-method (a) in the manual
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
#F  RcwaMapping( <R>, <coeffs> ) . . . . . . . . . . method (b) in the manual
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
#F  RcwaMappingNC( <R>, <coeffs> ) . . . . . . .  NC-method (b) in the manual
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
#F  RcwaMapping( <coeffs> ) . . . . . . . . . . . .  method (c) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping of Z by coefficients (RCWA)",
               true, [ IsList ], 0,

  function ( coeffs )

    local  quiet;

    if not IsList( coeffs[1] ) or not IsInt( coeffs[1][1] )
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
#F  RcwaMappingNC( <coeffs> ) . . . . . . . . . . NC-method (c) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping of Z by coefficients (RCWA)",
               true, [ IsList ], 0,

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
      f!.coeffs  := Immutable(cRed);
      f!.modulus := Length(cRed);
    end;

    if not IsList( coeffs[1] ) or not IsInt( coeffs[1][1] )
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
#F  RcwaMapping( <perm>, <range> ) . . . . . . . . . method (d) in the manual
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
#F  RcwaMappingNC( <perm>, <range> ) . . . . . .  NC-method (d) in the manual
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
#F  RcwaMapping( <modulus>, <values> ) . . . . . . . method (e) in the manual
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
    if not ForAll(values,t -> t[1]^f = t[2])
    then if quiet then return fail; fi;
         Error("the values ",values," do not define a proper ",
               "rcwa mapping of Z.\n"); 
    fi;
    return f;
  end );

#############################################################################
##
#F  RcwaMappingNC( <modulus>, <values> ) . . . .  NC-method (e) in the manual
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
#F  RcwaMapping( <pi>, <coeffs> ) . . . . . . . . .  method (f) in the manual
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
#F  RcwaMappingNC( <pi>, <coeffs> ) . . . . . . . NC-method (f) in the manual
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
      f!.coeffs  := Immutable(cRed[1]);
      f!.modulus := Length(cRed[1]);
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
#F  RcwaMapping( <q>, <modulus>, <coeffs> ) . . . .  method (g) in the manual
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
#F  RcwaMappingNC( <q>, <modulus>, <coeffs> ) . . NC-method (g) in the manual
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
#F  RcwaMapping( <P1>, <P2> ) . . . . . . . . . . .  method (h) in the manual
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
#F  RcwaMappingNC( <P1>, <P2> ) . . . . . . . . . NC-method (h) in the manual
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
      r1 := Residues(P1[i])[1]; m1 := Modulus(P1[i]);
      r2 := Residues(P2[i])[1]; m2 := Modulus(P2[i]);
      for j in Filtered([1..Length(res)],j->res[j] mod m1 = r1) do
        coeffs[j] := [m2,m1*r2-m2*r1,m1];
      od;
    od;
    return RcwaMappingNC(R,m,coeffs);
  end );

#############################################################################
##
#F  RcwaMapping( <cycles> ) . . . . . . . . . . . .  method (i) in the manual
##
InstallMethod( RcwaMapping,
               "rcwa mapping by class cycles (RCWA)", true, [ IsList ], 0,

  function ( cycles )

    local  CheckClassCycles, R;

    CheckClassCycles := function ( R, cycles )

      if not (    ForAll(cycles,IsList)
              and ForAll(Flat(cycles),S->IsResidueClass(S)
              and IsSubset(R,S)))
         or  ForAny(Combinations(Flat(cycles),2),
                    s->Intersection(s[1],s[2]) <> [])
      then Error("there is no rcwa mapping of ",R," having the class ",
                 "cycles ",cycles,".\n"); 
      fi;
    end;

    if   not IsList(cycles[1]) or not IsResidueClassUnion(cycles[1][1])
    then TryNextMethod(); fi;
    R := UnderlyingRing(FamilyObj(cycles[1][1]));
    CheckClassCycles(R,cycles);
    return RcwaMappingNC(cycles);
  end );

#############################################################################
##
#F  RcwaMappingNC( <cycles> ) . . . . . . . . . . NC-method (i) in the manual
##
InstallMethod( RcwaMappingNC,
               "rcwa mapping by class cycles (RCWA)", true, [ IsList ], 0,

  function ( cycles )

    local  result, R, coeffs, m, res, cyc, pre, im, affectedpos,
           r1, r2, m1, m2, pos, i;

    if not IsResidueClassUnion(cycles[1][1]) then TryNextMethod(); fi;

    R      := UnderlyingRing(FamilyObj(cycles[1][1]));
    m      := Lcm(List(Union(cycles),Modulus));
    res    := AllResidues(R,m);
    coeffs := List(res,r->[1,0,1]*One(R));
    for cyc in cycles do
      if Length(cyc) <= 1 then continue; fi;
      for pos in [1..Length(cyc)] do
        pre := cyc[pos]; im := cyc[pos mod Length(cyc) + 1];
        r1 := Residues(pre)[1]; m1 := Modulus(pre);
        r2 := Residues(im )[1]; m2 := Modulus(im);
        affectedpos := Filtered([1..Length(res)],i->res[i] mod m1 = r1);
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
    Assert(1,Order(result)=Lcm(List(cycles,Length)));
    SetIsBijective(result,true); SetIsTame(result,true);
    SetOrder(result,Lcm(List(cycles,Length)));
    return result;
  end );

#############################################################################
##
#S  Translating rcwa mappings of Z to rcwa mappings of Z_(pi). //////////////
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
#S  Constructors for special types of rcwa permutations. ////////////////////
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
##  Enclosing the argument list in list brackets is permitted.
##
InstallGlobalFunction( ClassShift,

  function ( arg )

    local  result, R, coeff, idcoeff, res, pos, r, m;

    if IsList(arg[1]) then arg := arg[1]; fi;

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
    SetName(result,Concatenation("ClassShift(",String(r),",",String(m),")"));
    SetLaTeXName(result,Concatenation("\\nu_{",String(r),"(",
                                               String(m),")}"));
    SetFactorizationIntoCSCRCT(result,[result]);
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
#F  ClassReflection( <R>, <r>, <m> )  . . . .  class reflection varsigma_r(m)
#F  ClassReflection( <r>, <m> ) . . . . . . . . . . . . . . . . . . .  (dito)
#F  ClassReflection( <R>, <cl> )  . class reflection varsigma_r(m), cl = r(m)
#F  ClassReflection( <cl> ) . . . . . . . . . . . . . . . . . . . . .  (dito)
#F  ClassReflection( <R> )  . . . . . .  class reflection varsigma_R: n -> -n
##
##  Enclosing the argument list in list brackets is permitted.
##
InstallGlobalFunction( ClassReflection,

  function ( arg )

    local  result, R, coeff, idcoeff, res, pos, r, m;

    if IsList(arg[1]) then arg := arg[1]; fi;

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
    SetName(result,Concatenation("ClassReflection(",
                                 String(r),",",String(m),")"));
    SetLaTeXName(result,Concatenation("\\varsigma_{",String(r),"(",
                                                     String(m),")}"));
    SetFactorizationIntoCSCRCT(result,[result]);
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
#F  ClassRotation( <R>, <r>, <m>, <u> ) . . . . . class rotation rho_(r(m),u)
#F  ClassRotation( <r>, <m>, <u> )  . . . . . . . . . . . . . . . . .  (dito)
#F  ClassRotation( <R>, <cl>, <u> ) .  class rotation rho_(r(m),u), cl = r(m)
#F  ClassRotation( <cl>, <u> )  . . . . . . . . . . . . . . . . . . .  (dito)
#F  ClassRotation( <R>, <u> ) . . . . . . . class rotation rho_(R,u): n -> un
##
##  Enclosing the argument list in list brackets is permitted.
##
InstallGlobalFunction( ClassRotation,

  function ( arg )

    local  result, R, coeff, idcoeff, res, pos, r, m, u;

    if IsList(arg[1]) then arg := arg[1]; fi;

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
    SetName(result,Concatenation("ClassRotation(",
                                 String(r),",",String(m),",",String(u),")"));
    SetLaTeXName(result,Concatenation("\\rho_{",String(r),"(",String(m),"),",
                                                String(u),"}"));
    SetFactorizationIntoCSCRCT(result,[result]);
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
#F  ClassTransposition( <R>, <r1>, <m1>, <r2>, <m2> ) . . class transposition
#F  ClassTransposition( <r1>, <m1>, <r2>, <m2>              tau_r1(m1),r2(m2)
#F  ClassTransposition( <R>, <cl1>, <cl2> ) ) . . dito, cl1=r1(m1) cl2=r2(m2)
#F  ClassTransposition( <cl1>, <cl2> ) )  . . . . . . . . . . . . . .  (dito)
##
##  Enclosing the argument list in list brackets is permitted.
##
InstallGlobalFunction( ClassTransposition,

  function ( arg )

    local  result, R, r1, m1, r2, m2, cl1, cl2, h;

    if IsList(arg[1]) then arg := arg[1]; fi;

    if not Length(arg) in [2..5]
      or     Length(arg) = 2 and not ForAll(arg,IsResidueClass)
      or     Length(arg) = 3
         and not (     IsRing(arg[1]) and ForAll(arg{[2,3]},IsResidueClass)
                   and arg[1] = UnderlyingRing(FamilyObj(arg[2]))
                   and arg[1] = UnderlyingRing(FamilyObj(arg[3])))
      or     Length(arg) = 4 and not ForAll(arg,IsRingElement)
      or     Length(arg) = 5 and not (    IsRing(arg[1])
                                      and IsSubset(arg[1],arg{[2..5]}))
    then Error("usage: see ?ClassTransposition( r1, m1, r2, m2 )\n"); fi;

    if IsRing(arg[1]) then R := arg[1]; arg := arg{[2..Length(arg)]}; fi;
    if   IsResidueClass(arg[1])
    then if not IsBound(R) then R := UnderlyingRing(FamilyObj(arg[1])); fi;
         arg := [Residue(arg[1]),Modulus(arg[1]),
                 Residue(arg[2]),Modulus(arg[2])] * One(R);
    elif not IsBound(R) then R := DefaultRing(arg{[2,4]}); fi;
    arg := arg * One(R); # Now we know R, and we have arg = [r1,m1,r2,m2].

    r1 := arg[1]; m1 := arg[2]; r2 := arg[3]; m2 := arg[4];

    if   IsZero(m1*m2) or IsZero((r1-r2) mod Gcd(m1,m2)) then
      Error("ClassTransposition: The residue classes must be disjoint.\n");
    fi;

    r1 := r1 mod m1; r2 := r2 mod m2;
    if   m1 > m2 or (m1 = m2 and r1 > r2)
    then h := r1; r1 := r2; r2 := h; h := m1; m1 := m2; m2 := h; fi;
    cl1    := ResidueClass(R,m1,r1);
    cl2    := ResidueClass(R,m2,r2);
    result := RcwaMapping([[cl1,cl2]]);
    SetIsClassTransposition(result,true);
    SetTransposedClasses(result,[cl1,cl2]);
    SetName(result,Concatenation("ClassTransposition(",
                                 String(r1),",",String(m1),",",
                                 String(r2),",",String(m2),")"));
    SetLaTeXName(result,
                 Concatenation("\\tau_{",String(r1),"(",String(m1),"),",
                                         String(r2),"(",String(m2),")}"));
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
    cls := AsUnionOfFewClasses(Support(sigma));
    if Length(cls) = 1 then cls := SplittedClass(cls[1],2); fi;
    if Length(cls) > 2 then return false; fi;
    if   sigma = ClassTransposition(cls)
    then SetTransposedClasses(sigma,cls); return true;
    else return false; fi;
  end );

#############################################################################
##
#M  TransposedClasses( <sigma> ) . . . . . . . . . . for class transpositions
##
InstallMethod( TransposedClasses,
               "for class transpositions (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( ct )
    if   IsClassTransposition(ct)
    then return TransposedClasses(ct);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  SplittedClassTransposition( <ct>, <k> ) . . . . . . .  2-argument version
##
InstallMethod( SplittedClassTransposition,
               "default method (RCWA)", ReturnTrue,
               [ IsRcwaMapping and IsClassTransposition,
                 IsRingElement ], 0,
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
                 IsRingElement, IsBool ], 0,

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
#F  ClassPairs( [ <R> ], <m> )
##
##  In the one-argument version, this function returns a list of all
##  unordered pairs of disjoint residue classes of Z with modulus <= <m>.
##
##  In the two-argument version, it does the following:
##
##    - If <R> is either the ring of integers or a semilocalization thereof,
##      it returns a list of all unordered pairs of disjoint residue classes
##      of <R> with modulus <= <m>.
##
##    - If <R> is a univariate polynomial ring over a finite field, it
##      returns a list of all unordered pairs of disjoint residue classes
##      of <R> whose moduli have degree less than <m>.
##
##  The purpose of this function is to generate a list of all
##  class transpositions whose moduli do not exceed a given bound.
##
InstallGlobalFunction( ClassPairs,

  function ( arg )

    local  R, m, tuples, moduli, Degree, m1, r1, m2, r2;

    if   Length(arg) = 1 then R := Integers; m := arg[1];
    elif Length(arg) = 2 then R := arg[1];   m := arg[2];
    else Error("usage: ClassPairs( [ <R> ], <m> )\n"); fi;
    if IsIntegers(R) or IsZ_pi(R) then
      tuples := Filtered(Cartesian([0..m-1],[1..m],[0..m-1],[1..m]),
                         t -> t[1] < t[2] and t[3] < t[4] and t[2] <= t[4]
                              and (t[1]-t[3]) mod Gcd(t[2],t[4]) <> 0
                              and (t[2] <> t[4] or t[1] < t[3]));
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
          if Degree(m1) > Degree(m2) then continue; fi;
          for r1 in AllResidues(R,m1) do
            for r2 in AllResidues(R,m2) do
              if (m1 <> m2 or r1 < r2) and not IsZero((r1-r2) mod Gcd(m1,m2))
              then Add(tuples,[r1,m1,r2,m2]); fi;
            od;
          od;
        od;
      od;
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
#F  PrimeSwitch( <p> ) . .  rcwa mapping of Z with multiplier p and divisor 2
#F  PrimeSwitch( <p>, <k> )
##
InstallGlobalFunction( PrimeSwitch,

  function ( arg )

    local  p, k, result, facts, kstr;

    if not Length(arg) in [1,2] then Error("usage: see ?PrimeSwitch\n"); fi;
    p := arg[1]; if Length(arg) = 2 then k := arg[2]; else k := 1; fi;
    if   not IsPosInt(p) or not IsPrimeInt(p) or not IsPosInt(k)
    then Error("usage: see ?PrimeSwitch\n"); fi;
    facts := [ ClassTransposition(k,2*k*p,0,8*k),
               ClassTransposition(2*k*p-k,2*k*p,4*k,8*k),
               ClassTransposition(0,4*k,k,2*k*p),
               ClassTransposition(2*k,4*k,2*k*p-k,2*k*p),
               ClassTransposition(2*k,2*k*p,k,4*k*p),
               ClassTransposition(4*k,2*k*p,2*k*p+k,4*k*p) ];
    result := Product(facts); SetIsPrimeSwitch(result,true);
    SetIsTame(result,false); SetOrder(result,infinity);
    if k = 1 then kstr := ""; else kstr := Concatenation(",",String(k)); fi;
    SetName(result,Concatenation("PrimeSwitch(",String(p),kstr,")"));
    SetLaTeXName(result,Concatenation("\\sigma_{",String(p),kstr,"}"));
    SetFactorizationIntoCSCRCT(result,facts);
    return result;
  end );

#############################################################################
##
#M  IsPrimeSwitch( <sigma> ) . . . . . . . . . . . . . for rcwa mappings of Z
##
InstallMethod( IsPrimeSwitch,
               "for rcwa mappings of Z (RCWA)", 
               true, [ IsRcwaMappingOfZ ], 0,
               sigma -> Multiplier(sigma) > 2 and IsPrime(Multiplier(sigma))
                        and sigma = PrimeSwitch(Multiplier(sigma)) );

#############################################################################
##
#F  mKnot( <m> ) . . . . . . . .  an rcwa mapping of Timothy P. Keller's type
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
    SetLaTeXName(result,Concatenation("\\kappa_{",String(m),"}"));
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
               [ IsRcwaMappingOfZInStandardRep ], 0,

  function ( arg )

    local f, lng, s;

    f := arg[1]; if Length(arg) > 1 then lng := arg[2]; fi;
    s := Concatenation( "RcwaMapping( ", String( f!.coeffs ), " )" );
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
                        String(f!.coeffs), " )" );
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
                        String(f!.modulus), ", ", String(f!.coeffs), " )" );
    if IsBound(lng) then s := String(s,lng); fi;
    return s;
  end );

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( PrintObj,
               "for rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZInStandardRep ], SUM_FLAGS,

  function ( f )
    Print( "RcwaMapping( ", f!.coeffs, " )" );
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
           NoninvertiblePrimes(Source(f)), ", ", f!.coeffs, " )" );
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
           ", ", f!.modulus, ", ", f!.coeffs, " )" );
  end );

#############################################################################
##
#M  ViewObj( <f> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( ViewObj,
               "for rcwa mappings (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )

    if IsZero(f) or IsOne(f) then View(f); return; fi;
    if IsOne(Modulus(f)) then Display(f:NoLineFeed); return; fi;
    Print("<");
    if   HasIsTame(f) and not (HasOrder(f) and IsInt(Order(f)))
    then if IsTame(f) then Print("tame "); else Print("wild "); fi; fi;
    if   HasIsBijective(f) and IsBijective(f)
    then Print("bijective ");
    elif HasIsInjective(f) and IsInjective(f)
    then Print("injective ");
    elif HasIsSurjective(f) and IsSurjective(f)
    then Print("surjective ");
    fi;
    Print("rcwa mapping of ",RingToString(Source(f)));
    Print(" with modulus ",f!.modulus);
    if   HasOrder(f) and not (HasIsTame(f) and not IsTame(f))
    then Print(", of order ",Order(f)); fi;
    Print(">");
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
##  Display the rcwa mapping <f> as a nice, human-readable table.
##
InstallMethod( Display,
               "for rcwa mappings (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )

    local  DisplayAffineMappingWithCoeffsInZ,
           DisplayAffineMappingWithCoeffsInZ_pi,
           DisplayAffineMappingWithCoeffsInGFqx, IdChars,
           m, c, pi, q, d, x, RingString, name, VarName,
           r, NrResidues, poses, pos, t, i, scr, l1, l2, l3, str,
           mdec, mstr, MaxPolLng, FlushLng, prefix;

    IdChars := function ( n, ch )
      return Concatenation( ListWithIdenticalEntries( n, ch ) );
    end;

    DisplayAffineMappingWithCoeffsInZ := function ( t )

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

    DisplayAffineMappingWithCoeffsInZ_pi := function ( t )

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

    DisplayAffineMappingWithCoeffsInGFqx := function ( t, maxlng )

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

    if   ValueOption("xdvi") = true and IsIntegers(Source(f))
    then LaTeXAndXDVI(f); return; fi;
    m := f!.modulus; c := f!.coeffs;
    if HasName(f) then
      name := Name(f);
      if   Position(name,'^') <> fail
      then name := Concatenation("(",name,")"); fi;
    else name := "f"; fi;
    prefix := false; RingString := RingToString(Source(f));
    if   IsRcwaMappingOfGFqx(f)
    then VarName := "P"; q := Size(UnderlyingField(f));
         d := DegreeOfLaurentPolynomial(m); NrResidues := q^d;
         x := IndeterminatesOfPolynomialRing(Source(f))[1];
         r := AllGFqPolynomialsModDegree(q,d,x);
         MaxPolLng := Maximum(List(r,p->Length(String(p))));
    else VarName := "n"; NrResidues := m; fi;
    if   IsOne(f)
    then Print("Identity rcwa mapping of ",RingString);
    elif IsZero(f)
    then Print("Zero rcwa mapping of ",RingString);
    elif IsOne(m) and IsZero(c[1][1])
    then Print("Constant rcwa mapping of ",RingString,
               " with value ",c[1][2]);
    else if not IsOne(m) then Print("\n"); fi;
         if HasIsTame(f) and not (HasOrder(f) and IsInt(Order(f))) then
           if IsTame(f) then Print("Tame "); else Print("Wild "); fi;
           prefix := true;
         fi;
         if   HasIsBijective(f) and IsBijective(f)
         then if prefix then Print("bijective ");
                        else Print("Bijective "); fi;
              prefix := true;
         elif HasIsInjective(f) and IsInjective(f)
         then if prefix then Print("injective ");
                        else Print("Injective "); fi;
              prefix := true;
         elif HasIsSurjective(f) and IsSurjective(f)
         then if prefix then Print("surjective ");
                        else Print("Surjective "); fi;
              prefix := true;
         fi;
         if prefix then Print("rcwa"); else Print("Rcwa"); fi;
         Print(" mapping of ",RingString);
         if IsOne(m) then
           Print(": ",VarName," -> ");
           if   IsRcwaMappingOfZ(f)
           then DisplayAffineMappingWithCoeffsInZ(c[1]);
           elif IsRcwaMappingOfZ_pi(f)
           then DisplayAffineMappingWithCoeffsInZ_pi(c[1]);
           else
             DisplayAffineMappingWithCoeffsInGFqx(c[1],SizeScreen()[1]-48);
           fi;
         else
           Print(" with modulus ",m);
           if   HasOrder(f) and not (HasIsTame(f) and not IsTame(f))
           then Print(", of order ",Order(f)); fi;
           Print("\n\n");
           scr := SizeScreen()[1] - 2;
           if   IsRcwaMappingOfZOrZ_pi(f)
           then l1 := Int(scr/2); else l1 := Int(scr/3); fi;
           mstr := String(m);
           if l1 - Length(mstr) - 6 <= 0 then mstr := "<modulus>"; fi;
           mdec := Length(mstr);
           l2 := Int((l1 - mdec - 6)/2);
           l3 := Int((scr - l1 - Length(name) - 3)/2);
           if   IsRcwaMappingOfZOrZ_pi(f)
           then FlushLng := l1-mdec-1; else FlushLng := l1-MaxPolLng-1; fi;
           Print(IdChars(l2," "),VarName," mod ",mstr,
                 IdChars(l1-l2-mdec-6," "),"|",IdChars(l3," "),VarName,"^",
                 name,"\n",IdChars(l1,"-"),"+",IdChars(scr-l1-1,"-"));
           poses := AsSortedList(List(Set(c),
                                      t -> Filtered([0..NrResidues-1],
                                                    i -> c[i+1] = t)));
           for pos in poses do
             str := " ";
             for i in pos do
               if   IsRcwaMappingOfZOrZ_pi(f)
               then Append(str,String(i,mdec+1));
               else Append(str,String(r[i+1],-(MaxPolLng+1))); fi;
               if Length(str) >= FlushLng then
                 if   Length(str) < l1
                 then Print("\n",String(str, -l1),"| ");
                 else Print("\n",String(" < ... > ",-l1),"| "); fi;
                 str := " ";
               fi;
             od;
             if   str <> " " 
             then Print("\n",String(str, -l1),"| "); fi;
             if   IsRcwaMappingOfZ(f)
             then DisplayAffineMappingWithCoeffsInZ(c[pos[1]+1]);
             elif IsRcwaMappingOfZ_pi(f)
             then DisplayAffineMappingWithCoeffsInZ_pi(c[pos[1]+1]);
             else
               DisplayAffineMappingWithCoeffsInGFqx(c[pos[1]+1],scr-l1-4);
             fi;
           od;
           Print("\n");
         fi;
    fi;
    if ValueOption("NoLineFeed") <> true then Print("\n"); fi;
  end );

#############################################################################
##
#M  LaTeXObj( <f> ) . . . . . . . . . . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( LaTeXObj,
               "for rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ ], 0,

  function ( f )

    local  LaTeXAffineMappingWithCoeffsInZ, append,
           c, m, mred, german, str, affs, maxafflng, t, poses, pos,
           res, src, cls, cl, indent, gens, i, j;

    append := function ( arg )
      str := CallFuncList(Concatenation,
                          Concatenation([str],List(arg,String)));
    end;

    LaTeXAffineMappingWithCoeffsInZ := function ( t )

      local  german, str, a, b, c, append;

      append := function ( arg )
        str := CallFuncList(Concatenation,
                            Concatenation([str],List(arg,String)));
      end;

      german := ValueOption("german") = true;
      a := t[1]; b := t[2]; c := t[3]; str := "";
      if   c = 1
      then if   a = 0
           then append(b);
           else if   AbsInt(a) <> 1 then append(a);
                elif a = -1         then append("-");
                fi;
                append("n");
                if   b > 0 then append(" + ", b);
                elif b < 0 then append(" - ",-b);
                fi;
           fi;
      elif b = 0 then if german then append("\\linfrac{"); fi;
                      if   AbsInt(a) <> 1 then append(a);
                      elif a = -1         then append("-");
                      fi;
                      append("n");
                      if german then append("}{"); else append("/"); fi;
                      append(c);
                      if german then append("}"); fi;
      else if german then append("\\afffrac{");
                     else append("("); fi;
           if   AbsInt(a) <> 1 then append(a);
           elif a = -1         then append("-");
           fi;
           append("n");
           if   b > 0 then append(" + ", b);
           elif b < 0 then append(" - ",-b);
           fi;
           if german then append("}{"); else append(")/"); fi;
           append(c);
           if german then append("}"); fi;
      fi;
      return str;
    end;

    if HasLaTeXName(f) then return LaTeXName(f); fi;
    indent := ValueOption("Indentation");
    if not IsPosInt(indent)
    then indent := ""; else indent := String(" ",indent); fi;
    str := indent;
    if ValueOption("Factorization") = true and IsBijective(f) then
      gens := List(FactorizationIntoCSCRCT(f),LaTeXName);
      append("      &");
      for pos in [1..Length(gens)] do
        append(gens[pos]);
        if pos < Length(gens) then
          if pos mod 5 = 0 then append(" \\\\\n"); fi;
          if pos mod 5 in [2,4] then append("\n"); fi;
          append(" \\cdot ");
          if pos mod 5 = 0 then append("&"); fi;
        else append("\n"); fi;
      od;
      return str;
    fi;
    german := ValueOption("german") = true;
    c := Coefficients(f); m := Length(c);
    if m = 1 then
      return Concatenation("n \\ \\mapsto \\ ",
                           LaTeXAffineMappingWithCoeffsInZ(c[1]));
    fi;
    append("n \\ \\longmapsto \\\n",indent,"\\begin{cases}\n");
    poses := AsSortedList( List( Set(c),
                                 t -> Filtered( [0..m-1],
                                                i -> c[i+1] = t ) ) );
    affs := List( c, LaTeXAffineMappingWithCoeffsInZ );
    maxafflng := Maximum( List( affs, Length ) );
    for pos in poses do
      append( indent, "  ", affs[ pos[1] + 1 ],
              String( "", maxafflng - Length( affs[pos[1]+1] ) ) );
      if german then append(" & \\falls n \\in ");
                else append(" & \\text{if} \\ n \\in "); fi;
      mred := Minimum( Filtered( DivisorsInt(m),
                                 d -> ForAll(Collected(List(pos,j->j mod d)),
                                             t -> t[2] = m/d) ) );
      res := Set( List( pos, j -> j mod mred ) );
      src := ResidueClassUnion(Integers,mred,res);
      cls := AsUnionOfFewClasses(src);
      for cl in cls do
        append(Residues(cl)[1],"(",Modulus(cl),")");
        if cl <> cls[Length(cls)] then append(" \\cup "); fi;
      od;
      if   pos = poses[ Length(poses) ]
      then append(".\n");
      else append(", \\\\\n"); fi;
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
    str := LaTeXObj(f:Indentation:=2);
    AppendTo(stream,str,"\\end{align*}");
    if HasIsTame(f) then
      if IsTame(f) then AppendTo(stream,"\nThis mapping is tame.");
                   else AppendTo(stream,"\nThis mapping is wild."); fi;
    fi;
    if HasOrder(f) then
      AppendTo(stream,"\nThe order of this mapping is \\(",
               LaTeXObj(Order(f)),"\\).");
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
#M  LaTeXObj( infinity ) . . . . . . . . . . . . . . . . . . . . for infinity
##
InstallMethod( LaTeXObj, "for infinity (RCWA)", true, [ IsInfinity ], 0,
               inf -> "\\infty" );

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
               "for two rcwa mappings of Z or Z_(pi) (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZOrZ_piInStandardRep,
                 IsRcwaMappingOfZOrZ_piInStandardRep ], 0,

  function ( f, g )
    return f!.coeffs = g!.coeffs;
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
#M  \<( <f>, <g> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
##  Total ordering of rcwa maps (for tech. purposes, only).
##  Separate methods are needed as soon as there are other representations of
##  rcwa mappings than by modulus <modulus> and coefficients list <coeffs>.
##
InstallMethod( \<,
               "for two rcwa mappings (RCWA)", IsIdenticalObj,
               [ IsRcwaMappingInStandardRep, IsRcwaMappingInStandardRep ], 0,

  function ( f, g )
    if   f!.modulus <> g!.modulus
    then return f!.modulus < g!.modulus;
    else return f!.coeffs  < g!.coeffs; fi;
  end );

#############################################################################
##
#S  On the zero- and the identity rcwa mapping. /////////////////////////////
##
#############################################################################

#############################################################################
##
#V  ZeroRcwaMappingOfZ . . . . . . . . . . . . . . . . zero rcwa mapping of Z
##
InstallValue( ZeroRcwaMappingOfZ, RcwaMapping( [ [ 0, 0, 1 ] ] ) );
SetIsZero( ZeroRcwaMappingOfZ, true );

#############################################################################
##
#M  Zero( <f> ) . . . . . . . . . . . . . . . . . . .  for rcwa mappings of Z
##
##  Zero rcwa mapping of Z.
##
InstallMethod( Zero,
               "for rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZInStandardRep ], 0,
               f -> ZeroRcwaMappingOfZ );

#############################################################################
##
#M  Zero( <f> ) . . . . . . . . . . . . . . . . . for rcwa mappings of Z_(pi)
##
##  Zero rcwa mapping of Z_(pi).
##
InstallMethod( Zero,
               "for rcwa mappings of Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZ_piInStandardRep ], 0,

  function ( f )

    local  zero;

    zero := RcwaMappingNC( NoninvertiblePrimes(Source(f)), [[0,0,1]] );
    SetIsZero( zero, true ); return zero;
  end );

#############################################################################
##
#M  Zero( <f> ) . . . . . . . . . . . . . . . . for rcwa mappings of GF(q)[x]
##
##  Zero rcwa mapping of GF(q)[x].
##
InstallMethod( Zero,
               "for rcwa mappings of GF(q)[x] (RCWA)",
               true, [ IsRcwaMappingOfGFqxInStandardRep ], 0,

  function ( f )

    local  zero;

    zero := RcwaMappingNC( Size(UnderlyingField(f)), One(Source(f)),
                           [[0,0,1]] * One(Source(f)) );
    SetIsZero( zero, true ); return zero;
  end );

#############################################################################
## 
#M  IsZero( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mappings
## 
##  <f> = zero rcwa mapping ? 
## 
InstallMethod( IsZero,
               "for rcwa mappings (RCWA)", true,
               [ IsRcwaMappingInStandardRep ], 0,
               f -> f!.coeffs = [ [ 0, 0, 1 ] ] * One( Source( f ) ) );  

#############################################################################
##
#V  IdentityRcwaMappingOfZ . . . . . . . . . . . . identity rcwa mapping of Z
##
InstallValue( IdentityRcwaMappingOfZ, RcwaMapping( [ [ 1, 0, 1 ] ] ) );
SetIsOne( IdentityRcwaMappingOfZ, true );

#############################################################################
##
#M  One( <f> ) . . . . . . . . . . . . . . . . . . . . for rcwa mappings of Z
##
##  Identity rcwa mapping of Z.
##
InstallMethod( One,
               "for rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZInStandardRep ], 0,
               f -> IdentityRcwaMappingOfZ );

#############################################################################
##
#M  One( <f> ) . . . . . . . . . . . . . . . . .  for rcwa mappings of Z_(pi)
##
##  Identity rcwa mapping of Z_(pi).
##
InstallMethod( One,
               "for rcwa mappings of Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZ_piInStandardRep ], 0,

  function ( f )

    local  one;

    one := RcwaMappingNC( NoninvertiblePrimes(Source(f)), [[1,0,1]] );
    SetIsOne( one, true ); return one;
  end );

#############################################################################
##
#M  One( <f> ) . . . . . . . . . . . . . . . .  for rcwa mappings of GF(q)[x]
##
##  Identity rcwa mapping of GF(q)[x].
##
InstallMethod( One,
               "for rcwa mappings of GF(q)[x] (RCWA)",
               true, [ IsRcwaMappingOfGFqxInStandardRep ], 0,

  function ( f )

    local  one;
 
    one := RcwaMappingNC( Size(UnderlyingField(f)), One(Source(f)),
                          [[1,0,1]] * One(Source(f)) );
    SetIsOne( one, true ); return one;
  end );

#############################################################################
## 
#M  IsOne( <f> ) . . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
## 
##  <f> = identity rcwa mapping?
##
InstallMethod( IsOne, 
               "for rcwa mappings (RCWA)", true,
               [ IsRcwaMappingInStandardRep ], 0,
               f -> f!.coeffs = [ [ 1, 0, 1 ] ] * One( Source( f ) ) );  

#############################################################################
##
#S  Accessing the components of an rcwa mapping object. /////////////////////
##
#############################################################################

#############################################################################
##
#M  Modulus( <f> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( Modulus,
               "for rcwa mappings (RCWA)", true,
               [ IsRcwaMappingInStandardRep ], 0, f -> f!.modulus );

#############################################################################
##
#M  Coefficients( <f> ) . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( Coefficients,
               "for rcwa mappings (RCWA)", true,
               [ IsRcwaMappingInStandardRep ], 0, f -> f!.coeffs );

#############################################################################
##
#S  Methods for the attributes and properties derived from the coefficients.
##
#############################################################################

#############################################################################
##
#M  Multiplier( <f> ) . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( Multiplier,
               "for rcwa mappings (RCWA)", true,
               [ IsRcwaMappingInStandardRep ], 0,
               f -> Lcm( UnderlyingRing( FamilyObj( f ) ),
                         List( f!.coeffs, c -> c[1] ) ) );

#############################################################################
##
#M  Multiplier( <f> ) . . . . . . . . . . . . . . for rcwa mappings of Z_(pi)
##
InstallMethod( Multiplier,
               "for rcwa mappings of Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZ_piInStandardRep ], 10,

  f -> Lcm( List( f!.coeffs,
                  c -> StandardAssociate( Source( f ), c[1] ) ) ) );

#############################################################################
##
#M  Divisor( <f> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( Divisor,
               "for rcwa mappings (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,
               f -> Lcm( UnderlyingRing( FamilyObj( f ) ),
                         List( f!.coeffs, c -> c[3] ) ) );

#############################################################################
##
#M  IsIntegral( <f> ) . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( IsIntegral,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               f -> IsOne( Divisor( f ) ) );

#############################################################################
##
#M  IsBalanced( <f> ) . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( IsBalanced,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  f -> Set( Factors( Multiplier( f ) ) ) = Set( Factors( Divisor( f ) ) ) );

#############################################################################
##
#M  PrimeSet( <f> ) . . . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( PrimeSet,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )
    if   IsZero(Multiplier(f))
    then Error("PrimeSet: Multiplier must not be zero.\n"); fi;
    return Filtered( Union(Set(Factors(Source(f),Modulus(f))),
                           Set(Factors(Source(f),Multiplier(f))),
                           Set(Factors(Source(f),Divisor(f)))),
                     x -> IsIrreducibleRingElement( Source( f ), x ) );
  end );

#############################################################################
##
#M  IsClassWiseOrderPreserving( <f> ) . . .  for rcwa mappings of Z or Z_(pi)
##
InstallMethod( IsClassWiseOrderPreserving,
               "for rcwa mappings of Z or Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZOrZ_piInStandardRep ], 0,
               f -> ForAll( f!.coeffs, c -> c[ 1 ] > 0 ) );

#############################################################################
##
#M  SetOnWhichMappingIsClassWiseOrderPreserving for rcwa map's of Z or Z_(pi)
#M  SetOnWhichMappingIsClassWiseOrderReversing  for rcwa map's of Z or Z_(pi)
#M  SetOnWhichMappingIsClassWiseConstant . . .  for rcwa map's of Z or Z_(pi)
##
InstallMethod( SetOnWhichMappingIsClassWiseOrderPreserving,
               "for rcwa mappings of Z or Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZOrZ_pi ], 0,
  f -> ResidueClassUnion( Source( f ), Modulus( f ),
                          Filtered( [ 0 .. Modulus( f ) - 1 ],
                                    r -> Coefficients( f )[r+1][1] > 0 ) ) );
InstallMethod( SetOnWhichMappingIsClassWiseOrderReversing,
               "for rcwa mappings of Z or Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZOrZ_pi ], 0,
  f -> ResidueClassUnion( Source( f ), Modulus( f ),
                          Filtered( [ 0 .. Modulus( f ) - 1 ],
                                    r -> Coefficients( f )[r+1][1] < 0 ) ) );
InstallMethod( SetOnWhichMappingIsClassWiseConstant,
               "for rcwa mappings of Z or Z_(pi) (RCWA)",
               true, [ IsRcwaMappingOfZOrZ_pi ], 0,
  f -> ResidueClassUnion( Source( f ), Modulus( f ),
                          Filtered( [ 0 .. Modulus( f ) - 1 ],
                                    r -> Coefficients( f )[r+1][1] = 0 ) ) );

#############################################################################
##
#M  IncreasingOn( <f> ) . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( IncreasingOn,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  R, m, c, numres;

    R := Source(f); m := Modulus(f); c := Coefficients(f);
    numres := Length(AllResidues(R,m));
    return ResidueClassUnion(R,m,
             AllResidues(R,m)
               {Filtered([1..numres], r -> Length(AllResidues(R,c[r][3]))
                                         < Length(AllResidues(R,c[r][1])))});
  end );

#############################################################################
##
#M  DecreasingOn( <f> ) . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( DecreasingOn,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  R, m, c, numres;

    R := Source(f); m := Modulus(f); c := Coefficients(f);
    numres := Length(AllResidues(R,m));
    return ResidueClassUnion(R,m,
            AllResidues(R,m)
              {Filtered([1..numres], r -> Length(AllResidues(R,c[r][3]))
                                        > Length(AllResidues(R,c[r][1])))});
  end );

#############################################################################
##
#M  LargestSourcesOfAffineMappings( <f> ) . . . . . . . . . for rcwa mappings
##
InstallMethod( LargestSourcesOfAffineMappings,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  P, R, m, c, clm, affs;

    R := Source(f); m := Modulus(f); c := Coefficients(f);
    affs := Set(c); clm  := AllResidueClassesModulo(R,m);
    P := List(affs,aff->Union(List(Filtered([1..Length(c)],i->c[i]=aff),
                                   j->clm[j]))); 
    return AsSortedList(P);
  end );

#############################################################################
##
#A  FixedPointsOfAffinePartialMappings( <f> ) for rcwa mapping of Z or Z_(pi)
##
InstallMethod( FixedPointsOfAffinePartialMappings,
               "for rcwa mappings of Z or Z_(pi) (RCWA)", true,
               [ IsRcwaMappingOfZOrZ_pi ], 0,

  function ( f )

    local  m, c, fixedpoints, r;

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
#M  ImageDensity( <f> ) . . . . . . . . . . . . . . . . . . for rcwa mappings
##
InstallMethod( ImageDensity,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  R, c, m;

    R := Source(f); c := Coefficients(f);
    m := Length(AllResidues(R,Modulus(f)));
    return Sum(List([1..m],r->Length(AllResidues(R,c[r][3]))/
                              Length(AllResidues(R,c[r][1]))))/m;
  end );

#############################################################################
##
#M  Multpk( <f>, <p>, <k> ) . . . . . . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( Multpk,
               "for rcwa mappings of Z (RCWA)",
               true, [ IsRcwaMappingOfZ, IsInt, IsInt ], 0,

  function ( f, p, k )

    local  m, c, res;

    m := Modulus(f); c := Coefficients(f);
    res := Filtered([0..m-1],r->PadicValuation(c[r+1][1]/c[r+1][3],p)=k);
    return ResidueClassUnion(Integers,m,res);
  end );

#############################################################################
##
#S  The support of an rcwa mapping. /////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  MovedPoints( <f> ) . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
##  The set of moved points (support) of the rcwa mapping <f>.
##
InstallMethod( MovedPoints,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  m, c, R, q, d, x, r, pols, residues, fixed, fixpoint;

    m := Modulus(f); c := Coefficients(f); R := Source(f);
    if   IsRcwaMappingOfZOrZ_pi(f)
    then pols     := [0..m-1]; # just a dummy
         residues := Filtered( [0..m-1], r -> c[r+1] <> [1,0,1] );
    else q    := Size(CoefficientsRing(R));
         d    := DegreeOfLaurentPolynomial(m);
         x    := IndeterminatesOfPolynomialRing(R)[1];
         pols := AllGFqPolynomialsModDegree(q,d,x);
         residues := Filtered( [0..q^d-1], r -> c[r+1] <> [1,0,1] * One(R) );
    fi;
    fixed := [];
    for r in residues do
      if c[r+1]{[1,3]} <> [1,1] * One(R) then
        fixpoint := c[r+1][2]/(c[r+1][3]-c[r+1][1]);
        if   fixpoint in R and fixpoint mod m = pols[r+1]
        then Add(fixed,fixpoint); fi;
      fi;
    od;
    if IsRcwaMappingOfGFqx(f) then residues := pols{residues+1}; fi;
    return ResidueClassUnion(R,m,residues,[],fixed);
  end );

#############################################################################
##
#M  NrMovedPoints( <obj> ) . . . . . . . . . . . . . . . . . . default method
##
InstallOtherMethod( NrMovedPoints,
                    "default method (RCWA)", true, [ IsObject ], 0,
                    obj -> Size( MovedPoints( obj ) ) );

#############################################################################
##
#M  Support( <g> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( Support,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               MovedPoints );

#############################################################################
##
#S  Restricting an rcwa mapping to a residue class union. ///////////////////
##
#############################################################################

#############################################################################
##
#M  RestrictedPerm( <g>, <S> )  for an rcwa mapping and a residue class union
##
InstallMethod( RestrictedPerm,
               "for an rcwa mapping and a residue class union (RCWA)",
               true, [ IsRcwaMapping, IsResidueClassUnion ], 0,

  function ( g, S )

    local  R, mg, mS, m, resg, resS, resm, cg, cgS, gS, r, pos;

    R := Source(g);
    if UnderlyingRing(FamilyObj(S)) <> R
      or IncludedElements(S) <> [] or ExcludedElements(S) <> []
      or not IsSubset(S,S^g)
    then TryNextMethod(); fi;
    mg := Modulus(g); mS := Modulus(S); m := Lcm(mg,mS);
    resg := AllResidues(R,mg); resS := Residues(S); resm := AllResidues(R,m);
    cg := Coefficients(g);
    cgS := List(resm,r->[1,0,1]*One(R));
    for pos in [1..Length(resm)] do
      r := resm[pos];
      if r mod mS in resS then
        cgS[pos] := cg[Position(resg,r mod mg)];
      fi;
    od;
    gS := RcwaMapping(R,m,cgS);
    return gS;
  end );

#############################################################################
##
#M  RestrictedPerm( <g>, <R> ) . . . . . . . . . . . . . .  for rcwa mappings
##
InstallMethod( RestrictedPerm,
               "for an rcwa mapping and its full source (RCWA)", true,
               [ IsRcwaMapping, IsRing ], 0,

  function ( g, R )
    if R = Source(g) then return g; else TryNextMethod(); fi;
  end );

#############################################################################
##
#S  Computing images under rcwa mappings. ///////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  ImageElm( <f>, <n> ) . . . . . .  for an rcwa mapping of Z and an integer
##
##  Image of the integer <n> under the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "for an rcwa mapping of Z and an integer (RCWA)",
               true, [ IsRcwaMappingOfZInStandardRep, IsInt ], 0,

  function ( f, n )

    local  m, c;

    m := f!.modulus; c := f!.coeffs[n mod m + 1];
    return (c[1] * n + c[2]) / c[3];
  end );

#############################################################################
##
#M  ImageElm( <f>, <n> ) . for an rcwa mapping of Z_(pi) and an el. of Z_(pi)
##
##  Image of the element <n> of the ring Z_(pi) for suitable <pi> under
##  the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               Concatenation("for an rcwa mapping of Z_(pi) ",
                             "and an element of Z_(pi) (RCWA)"),
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
##  Image of the polynomial <p> under the rcwa mapping <f>. 
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
##  Image of the ring element <n> under the rcwa mapping <f>. 
##
InstallMethod( \^,
               "for a ring element and an rcwa mapping (RCWA)",
               ReturnTrue, [ IsRingElement, IsRcwaMapping ], 0,

  function ( n, f )
    return ImageElm( f, n );
  end );

#############################################################################
##
#M  ImagesElm( <f>, <n> ) . . . . . .  for an rcwa mapping and a ring element
##
##  Images of the ring element <n> under the rcwa mapping <f>.
##  For technical purposes, only.
##
InstallMethod( ImagesElm,
               "for an rcwa mapping and a ring element (RCWA)",
               true, [ IsRcwaMapping, IsRingElement ], 0,

  function ( f, n )
    return [ ImageElm( f, n ) ];
  end ); 

#############################################################################
##
#M  ImagesSet( <f>, <S> ) . . . for an rcwa mapping and a residue class union
##
##  Image of the set <S> under the rcwa mapping <f>.
##
InstallMethod( ImagesSet,
               "for an rcwa mapping and a residue class union (RCWA)",
               true, [ IsRcwaMapping, IsListOrCollection ], 0,

  function ( f, S )

    local  R, c, m, rc, res, r;

    R := Source(f); if not IsSubset(R,S) then TryNextMethod(); fi;
    if IsList(S) then return Set(List(S,n->n^f)); fi;
    c := Coefficients(f); m := Modulus(f); res := AllResidues(R,m);
    rc := function(r,m) return ResidueClass(R,m,r); end;
    return Union(List([1..Length(res)],
                      r->(c[r][1]*Intersection(S,rc(res[r],m))+c[r][2])/
                          c[r][3]));
  end );

#############################################################################
##
#M  \^( <S>, <f> ) . . . . . for a set or class partition and an rcwa mapping
##
##  Image of the set or class partition <S> under the rcwa mapping <f>.
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
               ReturnTrue, [ IsListOrCollection, IsRcwaMapping ], 0,

  function ( S, f )
    if   IsSubset(Source(f),S)
    then return ImagesSet( f, S );
    elif IsList(S) and ForAll(S,set->IsSubset(Source(f),set))
    then return List(S,set->set^f);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  \^( <U>, <f> ) .  for union of res.-cl. with fixed rep's and rcwa mapping
##
##  Image of the union <U> of residue classes of Z with fixed representatives
##  under the rcwa mapping <f>.
##
InstallMethod( \^,
               Concatenation("for a union of residue classes with fixed ",
                             "rep's and an rcwa mapping (RCWA)"), ReturnTrue,
               [ IsUnionOfResidueClassesOfZWithFixedRepresentatives,
                 IsRcwaMappingOfZ ], 0,

  function ( U, f )

    local  cls, abc, m, c, k, l;

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
##  Preimage of the ring element <n> under the bijective rcwa mapping <f>.
##
InstallMethod( PreImageElm,
               "for a bijective rcwa mapping and a ring element (RCWA)",
               true, [ IsRcwaMapping and IsBijective, IsRingElement ], 0,

  function ( f, n )
    return n^Inverse( f );
  end );

#############################################################################
##
#M  PreImagesElm( <f>, <n> ) . . . .  for an rcwa mapping of Z and an integer
##
##  Preimages of the integer <n> under the rcwa mapping <f>. 
##
InstallMethod( PreImagesElm,
               "for an rcwa mapping of Z and an integer (RCWA)", true, 
               [ IsRcwaMappingOfZInStandardRep, IsInt ], 0,

  function ( f, n )
    
    local  c, m, preimage, modulus, residues, singletons, n1, pre;

    c := f!.coeffs; m := f!.modulus;
    preimage := []; singletons := [];
    for n1 in [1..m] do
      if c[n1][1] <> 0 then
        pre := (c[n1][3] * n - c[n1][2])/c[n1][1];
        if IsInt(pre) and pre mod m = n1 - 1 then Add(singletons,pre); fi;
      else
        if c[n1][2] = n then
          if   m = 1 then return Integers;
          else preimage := Union(preimage,ResidueClass(Integers,m,n1-1)); fi;
        fi;
      fi;
    od;
    preimage := Union(preimage,singletons);
    return preimage;
  end );

#############################################################################
##
#M  PreImagesRepresentative( <f>, <n> ) . . for rcwa mapping of Z and integer
##
##  A representative of the set of preimages of the integer <n> under the
##  rcwa mapping <f>. 
##
InstallMethod( PreImagesRepresentative,
               "for an rcwa mapping of Z and an integer (RCWA)", true, 
               [ IsRcwaMappingOfZInStandardRep, IsInt ], 0,

  function ( f, n )
    
    local  c, m, n1, pre;

    c := f!.coeffs; m := f!.modulus;
    for n1 in [1..m] do
      if c[n1][1] <> 0 then
        pre := (n * c[n1][3] - c[n1][2])/c[n1][1];
        if IsInt(pre) and pre mod m = n1 - 1 then return pre; fi;
      else
        if c[n1][2] = n then return n1 - 1; fi;
      fi;
    od;
    return fail;
  end );

#############################################################################
##
#M  PreImagesSet( <f>, <R> ) . .  for an rcwa mapping and its underlying ring
##
##  Preimage of the rcwa mapping <f>. For technical purposes, only.
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
InstallMethod( PreImagesSet,
               "for an rcwa mapping and a finite set (RCWA)",
               true, [ IsRcwaMapping, IsList ], 0,

  function ( f, l )
    return Union( List( Set( l ), n -> PreImagesElm( f, n ) ) );
  end );

#############################################################################
##
#M  PreImagesSet( <f>, <S> )  for an rcwa mapping of Z and a res. class union
##
##  Preimage of the residue class union <S> under the rcwa mapping <f>.
##
InstallMethod( PreImagesSet,
               "for an rcwa mapping of Z and a residue class union (RCWA)",
               true, [ IsRcwaMappingOfZ, IsResidueClassUnionOfZ ], 0,

  function ( f, S )

    local  preimage, parts, premod, preres, rump,
           pre, pre2, im, diff, excluded, n;

    rump := ResidueClassUnion( Integers, Modulus(S), Residues(S) );
    premod := Modulus(f) * Divisor(f) * Modulus(S);
    preres := Filtered( [ 0 .. premod ], n -> n^f in rump );
    parts := [ ResidueClassUnion( Integers, premod, preres ) ];
    Append( parts, List( IncludedElements(S), n -> PreImagesElm( f, n ) ) );
    preimage := Union( parts );
    excluded := ExcludedElements(S);
    for n in excluded do
      pre  := PreImagesElm( f, n );
      im   := ImagesSet( f, pre );
      pre2 := PreImagesSet( f, Difference( im, excluded ) );
      diff := Difference( pre, pre2 );
      if   diff <> [ ]
      then preimage := Difference( preimage, diff ); fi;
    od;
    return preimage;
  end );

#############################################################################
##
#M  PreImagesSet( <f>, <U> ) . . . . as above, but with fixed representatives
##
##  Preimage of the union <U> of residue classes of Z with fixed representa-
##  tives under the rcwa mapping <f>.
##
InstallMethod( PreImagesSet,
               Concatenation("for an rcwa mapping of Z and a union of ",
                             "residue classes with fixed rep's (RCWA)"),
               ReturnTrue,
               [ IsRcwaMappingOfZ,
                 IsUnionOfResidueClassesOfZWithFixedRepresentatives ], 0,

  function ( f, U )

    local  preimage, cls, rep, m, minv, clm, k, l;

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
##  Pointwise sum of the rcwa mappings <f> and <g>.
##
InstallMethod( \+,
               "for two rcwa mappings of Z or Z_(pi) (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZOrZ_piInStandardRep,
                 IsRcwaMappingOfZOrZ_piInStandardRep ], 0,

  function ( f, g )
    
    local c1, c2, c3, m1, m2, m3, n, n1, n2, pi;

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
#M  \+( <f>, <g> ) . . . . . . . . . . . .  for two rcwa mappings of GF(q)[x]
##
##  Pointwise sum of the rcwa mappings <f> and <g>.
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
##
##  Pointwise additive inverse of rcwa mapping <f>.
##
InstallMethod( AdditiveInverseOp,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               f -> f * RcwaMappingNC( Source(f), One(Source(f)),
                                       [[-1,0,1]] * One(Source(f)) ) );

#############################################################################
##
#M  \+( <f>, <n> ) . . . . . . . . . . for an rcwa mapping and a ring element
##
##  Pointwise sum of the rcwa mapping <f> and the constant rcwa mapping with
##  value <n>.
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

#############################################################################
##
#M  \+( <n>, <f> ) . . . . . . . . . . for a ring element and an rcwa mapping
##
InstallMethod( \+,
               "for a ring element and an rcwa mapping (RCWA)",
               ReturnTrue, [ IsRingElement, IsRcwaMapping ], 0,
               function ( n, f ) return f + n; end );

#############################################################################
##
#S  Multiplying rcwa mappings. //////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . .  for two rcwa mappings of Z or Z_(pi)
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for two rcwa mappings of Z or Z_(pi) (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfZOrZ_piInStandardRep,
                 IsRcwaMappingOfZOrZ_piInStandardRep ], SUM_FLAGS,

  function ( g, f )

    local  fg, c1, c2, c3, m1, m2, m3, n, n1, n2, pi;

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
#M  CompositionMapping2( <g>, <f> ) . . . . for two rcwa mappings of GF(q)[x]
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for two rcwa mappings of GF(q)[x] (RCWA)",
               IsIdenticalObj,
               [ IsRcwaMappingOfGFqxInStandardRep,
                 IsRcwaMappingOfGFqxInStandardRep ], SUM_FLAGS,

  function ( g, f )

    local  fg, c, m, d, R, q, x, res, r, n1, n2;

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
#M  \*( <n>, <f> ) . . . . .  for rcwa mappings, multiplication by a constant
#M  \*( <f>, <n> )
##
InstallMethod( \*,
               "for rcwa mappings, multiplication by a constant (RCWA)",
               ReturnTrue, [ IsRingElement, IsRcwaMapping ], 0,
               function ( n, f )
                 if not n in Source(f) then TryNextMethod(); fi;
                 return RcwaMapping( Source(f), One( Source(f) ),
                                    [ [ n, 0, 1 ] ] * One( Source(f) ) ) * f;
               end );
InstallMethod( \*,
               "for rcwa mappings, multiplication by a constant (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsRingElement ], 0,
               function ( f, n ) return n * f; end );

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
    if order = fail or order = infinity then
      return Concatenation(name,"^{",String(e),"}");
    elif e mod order = 1 then
      return name;
    elif e mod order = 0 then
      return fail;
    else
      return Concatenation(name,"^{",String(e mod order),"}");
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
##  Inverse mapping of bijective rcwa mapping <f>.
##
InstallMethod( InverseOp,
               "for rcwa mappings of Z or Z_(pi) (RCWA)", true,
               [ IsRcwaMappingOfZOrZ_piInStandardRep ], 0,
               
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
    if HasOrder(f) then SetOrder(Result,Order(f)); order := Order(f);
                   else order := fail; fi;
    if HasName(f) then
      SetName(Result,NAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                       Name(f),-1,order));
    fi;
    if HasLaTeXName(f) then
      SetLaTeXName(Result,LATEXNAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                            LaTeXName(f),-1,order));
    fi;

    return Result;
  end );

#############################################################################
##
#M  InverseOp( <f> ) . . . . . . . . . . . . .  for rcwa mappings of GF(q)[x]
##
##  Inverse mapping of bijective rcwa mapping <f>.
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
    if HasOrder(f) then SetOrder(Result,Order(f)); order := Order(f);
                   else order := fail; fi;
    if HasName(f) then
      SetName(Result,NAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                       Name(f),-1,order));
    fi;
    if HasLaTeXName(f) then
      SetLaTeXName(Result,LATEXNAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                            LaTeXName(f),n,order));
    fi;

    return Result;
  end );

#############################################################################
##
#M  InverseGeneralMapping( <f> ) . . . . . . . . . . . . .  for rcwa mappings
##
##  Inverse mapping of bijective rcwa mapping <f>.
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
#M  RightInverse( <f> ) . . . . . . . . . .  for injective rcwa mappings of Z
##
InstallMethod( RightInverse,
               "for injective rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ ], 0,

  function ( f )

    local  inv, mf, cf, minv, cinv, imgs, r1, r2;

    if not IsInjective(f) then return fail; fi;
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
##  Conjugate of the rcwa mapping <g> under <h>.
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
    return f;
  end );

#############################################################################
##
#M  \^( <perm>, <g> ) . . . . . .  for a permutation and an rcwa mapping of Z
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
##  <n>-th power of the rcwa mapping <f>. 
##
InstallMethod( \^,
               "for an rcwa mapping and an integer (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsInt ], 0,

  function ( f, n )

    local  pow, e, name, latexname;

    if ValueOption("UseKernelPOW") = true then TryNextMethod(); fi;

    if HasOrder(f) and Order(f) <> infinity then n := n mod Order(f); fi;

    if   n = 0 then return One(f);
    elif n = 1 then return f;
    else if n > 1 then pow := POW(f,n:UseKernelPOW);
                  else pow := POW(Inverse(f),-n:UseKernelPOW); fi;
    fi;

    if HasIsTame(f) then SetIsTame(pow,IsTame(f)); fi;

    if HasOrder(f) then
      if Order(f) = infinity then SetOrder(pow,infinity); else
        SetOrder(pow,Order(f)/Gcd(Order(f),n));
      fi;
      if HasName(f) and HasIsTame(f) and IsTame(f) then
        name := NAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(Name(f),n,Order(f));
        if name <> fail then SetName(pow,name); fi;
      fi;
      if HasLaTeXName(f) then
        latexname := LATEXNAME_OF_POWER_BY_NAME_EXPONENT_AND_ORDER(
                       LaTeXName(f),n,Order(f));
        if latexname <> fail then SetLaTeXName(pow,latexname); fi;
      fi;
    fi;

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

    local  gamma, delta, C, r,
           m, coeffs, cl, img, c, d,
           pow, exp, e;

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

    if not IsSubset(Factors(Multiplier(f)),Factors(Divisor(f))) then
      Info(InfoRCWA,3,"IsTame: <f> is wild, by Balancedness Criterion.");
      if IsBijective(f) then SetOrder(f,infinity); fi;
      return false;
    fi;

    if    IsBijective(f)
      and Set(Factors(Multiplier(f))) <> Set(Factors(Divisor(f)))
    then
      Info(InfoRCWA,3,"IsTame: <f> is wild, by Balancedness Criterion.");
      SetOrder(f,infinity); return false;
    fi;

    if IsSurjective(f) and not IsInjective(f) then
      Info(InfoRCWA,3,"IsTame: <f> is surjective and not ",
                      "injective, hence wild.");
      return false;
    fi;

    if IsRcwaMappingOfZOrZ_pi(f) and IsBijective(f) then
      Info(InfoRCWA,3,"IsTame: Sources-and-Sinks Criterion.");
      gamma := TransitionGraph(f,Modulus(f));
      for r in [1..Modulus(f)] do RemoveSet(gamma.adjacencies[r],r); od;
      delta := UnderlyingGraph(gamma);
      C := ConnectedComponents(delta);
      if Position(List(C,V->Diameter(InducedSubgraph(gamma,V))),-1) <> fail
      then
        Info(InfoRCWA,3,"IsTame: <f> is wild, ",
                        "by Sources-and-Sinks Criterion.");
        SetOrder(f,infinity); return false;
      fi;
    fi;

    if IsBijective(f) then
      Info(InfoRCWA,3,"IsTame: Loop Criterion.");
      m := Modulus(f);
      if IsRcwaMappingOfZ(f) then
        coeffs := Coefficients(f);
        for r in [0..m-1] do
          c := coeffs[r+1];
          if AbsInt(c[1]) <> 1 or c[3] <> 1 then
            d := Gcd(m,c[1]*m/c[3]);
            if (r - (c[1]*r+c[2])/c[3]) mod d = 0 then
              Info(InfoRCWA,3,"IsTame: <f> is wild, by Loop Criterion.");
              SetOrder(f,infinity); return false;
            fi;
          fi;
        od;
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
    pow := f; exp := [2,2,3,5,2,7,3,2,11,13,5,3,17,19,2]; e := 1;
    for e in exp do
      pow := pow^e;
      if IsIntegral(pow) then
        Info(InfoRCWA,3,"IsTame: <f> has a power which is integral, ",
                        "hence is tame.");
        return true;
      fi;
      if   IsRcwaMappingOfZOrZ_pi(f) and Modulus(pow) > 6 * Modulus(f)
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
#M  RespectedPartitionShort( <sigma> ) . . . for tame bijective rcwa mappings
##
InstallMethod( RespectedPartitionShort,
               "for tame bijective rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 0,

  function ( sigma )
    if not IsBijective(sigma) then return fail; fi;
    return RespectedPartitionShort( Group( sigma ) );
  end );

#############################################################################
##
#M  RespectedPartitionLong( <sigma> ) . . .  for tame bijective rcwa mappings
##
InstallMethod( RespectedPartitionLong,
               "for tame bijective rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 0,

  function ( sigma )
    if not IsBijective(sigma) then return fail; fi;
    return RespectedPartitionLong( Group( sigma ) );
  end );

#############################################################################
##
#M  PermutationOpNC( <sigma>, <P>, <act> ) . .  for rcwa map. and resp. part.
##
InstallMethod( PermutationOpNC,
               "for an rcwa mapping and a respected partition (RCWA)", true,
               [ IsRcwaMapping, IsList, IsFunction ], 0,

  function ( sigma, P, act )

    local  rep, img, i, j;

    if   act <> OnPoints or not ForAll(P,IsResidueClassUnion)
    then return PermutationOp(sigma,P,act); fi;
    rep := List(P,cl->Representative(cl)^sigma);
    img := [];
    for i in [1..Length(P)] do
      j := 0;
      repeat j := j + 1; until rep[i] in P[j];
      img[i] := j;
    od;
    return PermList(img);
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
           n0, n, b1, b2, m1, m2, r, pow, exp, c, i;

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
    fi;

    if Set(Factors(Multiplier(g))) <> Set(Factors(Divisor(g))) then
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
        if IsOne(pow) then return e; fi;
      fi;

    else # for rcwa permutations of rings other than Z or Z_(pi)

      e := Lcm(List(ShortCycles(g,AllResidues(Source(g),Modulus(g)^2),12),
                    Length));
      pow := g^e;
      if IsIntegral(pow) then SetIsTame(g,true); fi;
      if IsOne(pow) then return e; fi;

    fi;

    if not IsTame(g) then
      Info(InfoRCWA,3,"Order: <g> is wild, thus has infinite order.");
      return infinity;
    fi;

    Info(InfoRCWA,3,"Order: Attempt to determine a respected partition <P>");
    Info(InfoRCWA,3,"       of <g>, and compute the order <k> of the per-");
    Info(InfoRCWA,3,"       mutation induced by <g> on <P> as well as the");
    Info(InfoRCWA,3,"       order of <g>^<k>.");

    P := RespectedPartition(g);

    k      := Order(Permutation(g,P));
    gtilde := g^k;

    if IsOne(gtilde) then return k; fi;

    if IsRcwaMappingOfZOrZ_pi(g) then
      if   not IsClassWiseOrderPreserving(gtilde) and IsOne(gtilde^2)
      then return 2*k; else return infinity; fi;
    fi;

    if IsRcwaMappingOfGFqx(g) then
      e := Lcm(List(Coefficients(gtilde),c->Order(c[1])));
      gtilde := gtilde^e;
      if IsOne(gtilde) then return k * e; fi;
      p := Characteristic(Source(g));
      gtilde := gtilde^p;
      if IsOne(gtilde) then return k * e * p; fi;
    fi;

    Info(InfoRCWA,3,"Order: Giving up.");
    TryNextMethod();

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
    T := MutableNullMat(Length(Resm),Length(Resm));
    for n in ResmTest do
      i := Position(Resm,n   mod m);
      j := Position(Resm,n^f mod m);
      T[i][j] := T[i][j] + 1;
    od;
    return List(T,l->l/Sum(l));
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
##  The vertices are labelled by 1..<m> instead of 0..<m>-1 (0 is identified
##  with 1, etc.) because in {\GAP}, permutations cannot move 0.
##
##  The result is returned as a GRAPE graph.
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

#############################################################################
##
#S  Trajectories. ///////////////////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  Trajectory( <f>, <n>, <length> ) . . . . . . . . . for rcwa mappings, (1)
##
InstallMethod( Trajectory,
               "for an rcwa mapping, given number of iterates (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsObject, IsPosInt ], 0,

  function ( f, n, length )

    local  seq, step;

    if not (n in Source(f) or IsSubset(Source(f),n)) then TryNextMethod(); fi;
    seq := [n];
    for step in [1..length-1] do
      n := n^f;
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

    local  seq, step;

    if   not (n in Source(f) or IsSubset(Source(f),n)) or IsZero(m)
    then TryNextMethod(); fi;
    seq := [n mod m];
    for step in [1..length-1] do
      n := n^f;
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

    local  seq;

    if   not (n in Source(f) or IsSubset(Source(f),n))
      or not IsSubset(Source(f),terminal)
    then TryNextMethod(); fi;
    seq := [n];
    if   IsListOrCollection(n) or not IsListOrCollection(terminal)
    then terminal := [terminal]; fi;
    while not n in terminal do
      n := n^f;
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

    local  seq;

    if   not (n in Source(f) or IsSubset(Source(f),n))
      or not IsSubset(Source(f),terminal) or IsZero(m)
    then TryNextMethod(); fi;
    seq := [n mod m];
    if   IsListOrCollection(n) or not IsListOrCollection(terminal)
    then terminal := [terminal]; fi;
    while not n in terminal do
      n := n^f;
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

    if   IsPosInt(lngterm)           then length   := lngterm;
    elif IsListOrCollection(lngterm) then terminal := lngterm;
    else TryNextMethod(); fi;
    if not n in Source(f)
      or IsBound(terminal) and not IsSubset(Source(f),terminal)
      or not whichcoeffs in ["AllCoeffs","LastCoeffs"]
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
#F  TraceTrajectoriesOfClasses( <f>, <classes> ) . residue class trajectories
##
InstallGlobalFunction( TraceTrajectoriesOfClasses,

  function ( f, classes )

    local  l, k, starttime, timeout;

    l := [[classes]]; k := 1;
    starttime := Runtime(); timeout := ValueOption("timeout");
    if timeout = fail then timeout := infinity; fi;
    repeat
      Add(l,Flat(List(l[k],cl->AsUnionOfFewClasses(cl^f))));
      k := k + 1;
      Print("k = ",k,": "); View(l[k]); Print("\n");
    until Runtime() - starttime >= timeout or l[k] in l{[1..k-1]};
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
                       "See ?LikelyContractionCentre for information on ",
                       "how to improve this guess.");
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
#S  Finding finite cycles of an rcwa permutation. ///////////////////////////
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
    if   not IsBijective(sigma) or not IsSubset(Source(sigma),S)
    then TryNextMethod(); fi;
    return List(ShortOrbits(Group(sigma),S,maxlng),
                orb->Cycle(sigma,Minimum(orb)));
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
#S  Restriction monomorphisms and induction epimorphisms. ///////////////////
##
#############################################################################

#############################################################################
##
#M  Restriction( <g>, <f> ) . . . . . . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( Restriction,
               "for rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ, IsRcwaMappingOfZ ], 0,

  function ( g, f )

    local  gf;

    if not IsInjective(f) then return fail; fi;

    gf := RestrictedPerm( RightInverse(f) * g * f, Image(f) );

    Assert(1,g*f=f*gf,"Restriction: Diagram does not commute.\n");

    if HasIsInjective(g)  then SetIsInjective(gf,IsInjective(g)); fi;
    if HasIsSurjective(g) then SetIsSurjective(gf,IsSurjective(g)); fi;
    if HasIsTame(g)       then SetIsTame(gf,IsTame(g)); fi;
    if HasOrder(g)        then SetOrder(gf,Order(g)); fi;

    return gf;
  end );

#############################################################################
##
#M  Induction( <g>, <f> ) . . . . . . . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( Induction,
               "for rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ, IsRcwaMappingOfZ ], 0,

  function ( g, f )

    local  gf;

    if    not IsInjective(f) or not IsSubset(Image(f),MovedPoints(g))
       or not IsSubset(Image(f),MovedPoints(g)^g) then return fail; fi;

    gf := f * g * RightInverse(f);

    Assert(1,gf*f=f*g,"Induction: Diagram does not commute.\n");

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
        Info(InfoRCWA,1,"Dividing by ",Name(fact)," ",direction,".");
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
      Assert(2,IsBijective(RcwaMapping(ShallowCopy(Coefficients(g)))));
    end;

    if not IsBijective(g) then return fail; fi;
    if IsOne(g) then return [g]; fi;

    leftfacts := []; rightfacts := []; facts := []; elm := g;
    direction := ValueOption("Direction");
    if direction <> "from the left" then direction := "from the right"; fi;
    multswitches := []; divswitches := []; log := []; loop := false;

    if not IsClassWiseOrderPreserving(g) then

      Info(InfoRCWA,1,"Making the mapping class-wise order-preserving.");

      rev    := SetOnWhichMappingIsClassWiseOrderReversing(g);
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
        Assert(2,Union(P)=Integers);
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
        m := Modulus(rest); r := Residues(cl)[1];
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
#E  rcwamap.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here