#############################################################################
##
#W  rcwamap.gi                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains implementations of methods and functions for computing
##  with rcwa mappings of the ring of integers, its semilocalizations and of
##  polynomial rings in one variable over a finite field.
##
##  See the definitions given in the file `rcwamap.gd'.
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
#V  IntegralRcwaMappingsFamily . . . the family of all integral rcwa mappings
##
InstallValue( IntegralRcwaMappingsFamily,
              NewFamily( "RcwaMappingsFamily( Integers )",
                         IsIntegralRcwaMapping,
                         CanEasilySortElements, CanEasilySortElements ) );
SetFamilySource( IntegralRcwaMappingsFamily, FamilyObj( 1 ) );
SetFamilyRange ( IntegralRcwaMappingsFamily, FamilyObj( 1 ) );
SetUnderlyingRing( IntegralRcwaMappingsFamily, Integers );

# Internal variables storing the rcwa mapping families used in the
# current GAP session.

BindGlobal( "Z_PI_RCWAMAPPING_FAMILIES", [] );
BindGlobal( "MODULAR_RCWAMAPPING_FAMILIES", [] );

#############################################################################
##
#F  SemilocalIntegralRcwaMappingsFamily( <R> )
##
##  Family of semilocal integral rcwa mappings.
##
InstallGlobalFunction( SemilocalIntegralRcwaMappingsFamily,

  function ( R )

    local  fam, name;

    if   not IsZ_pi( R )
    then Error("usage: SemilocalIntegralRcwaMappingsFamily( <R> )\n",
               "where <R> = Z_pi( <pi> ) for a set of primes <pi>.\n");
    fi;
    fam := First( Z_PI_RCWAMAPPING_FAMILIES,
                  fam -> UnderlyingRing( fam ) = R );
    if fam <> fail then return fam; fi;
    name := Concatenation( "RcwaMappingsFamily( ",
                           String( R ), " )" );
    fam := NewFamily( name, IsSemilocalIntegralRcwaMapping,
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
#F  ModularRcwaMappingsFamily( <R> ) . . . .  family of modular rcwa mappings
##
InstallGlobalFunction( ModularRcwaMappingsFamily,

  function ( R )

    local  fam, x;

    if   not (     IsUnivariatePolynomialRing( R )
               and IsFiniteFieldPolynomialRing( R ) )
    then Error("usage: ModularRcwaMappingsFamily( <R> ) for a ",
               "univariate polynomial ring <R> over a finite field.\n");
    fi;
    x := IndeterminatesOfPolynomialRing( R )[ 1 ];
    fam := First( MODULAR_RCWAMAPPING_FAMILIES,
                  fam -> IsIdenticalObj( UnderlyingRing( fam ), R ) );
    if fam <> fail then return fam; fi;
    fam := NewFamily( Concatenation( "RcwaMappingsFamily( ",
                                      String( R ), " )" ),
                      IsModularRcwaMapping, CanEasilySortElements,
                      CanEasilySortElements );
    SetUnderlyingIndeterminate( fam, x );
    SetUnderlyingRing( fam, R );
    SetFamilySource( fam, FamilyObj( x ) );
    SetFamilyRange ( fam, FamilyObj( x ) );
    MakeReadWriteGlobal( "MODULAR_RCWAMAPPING_FAMILIES" );
    Add( MODULAR_RCWAMAPPING_FAMILIES, fam );
    MakeReadOnlyGlobal( "MODULAR_RCWAMAPPING_FAMILIES" );

    return fam;
  end );

#############################################################################
##
#F  RcwaMappingsFamily( <R> ) . . . family of rcwa mappings over the ring <R>
##
InstallGlobalFunction( RcwaMappingsFamily,

  function ( R )

    if   IsIntegers( R ) then return IntegralRcwaMappingsFamily;
    elif IsZ_pi( R )
    then return SemilocalIntegralRcwaMappingsFamily( R );
    elif IsUnivariatePolynomialRing( R ) and IsFiniteFieldPolynomialRing( R )
    then return ModularRcwaMappingsFamily( R );
    else Error("Sorry, rcwa mappings over ",R," are not yet implemented.\n");
    fi;
  end );

# Implications between types of rcwa mappings.

InstallTrueMethod( IsMapping,     IsRcwaMapping );
InstallTrueMethod( IsRcwaMapping, IsRationalBasedRcwaMapping );
InstallTrueMethod( IsRationalBasedRcwaMapping, IsIntegralRcwaMapping );
InstallTrueMethod( IsRationalBasedRcwaMapping,
                   IsSemilocalIntegralRcwaMapping );
InstallTrueMethod( IsRcwaMapping, IsModularRcwaMapping );

# Shorthands for commonly used filters.

BindGlobal( "IsRcwaMappingInStandardRep",
            IsRcwaMapping and IsRcwaMappingStandardRep );
BindGlobal( "IsIntegralRcwaMappingInStandardRep",
            IsIntegralRcwaMapping and IsRcwaMappingStandardRep );
BindGlobal( "IsSemilocalIntegralRcwaMappingInStandardRep",
            IsSemilocalIntegralRcwaMapping and IsRcwaMappingStandardRep );
BindGlobal( "IsRationalBasedRcwaMappingInStandardRep",
            IsRationalBasedRcwaMapping and IsRcwaMappingStandardRep );
BindGlobal( "IsModularRcwaMappingInStandardRep",
            IsModularRcwaMapping and IsRcwaMappingStandardRep );

# Bring the rcwa mapping <f> to normalized, reduced form.

ReduceIntegralRcwaMapping := function ( f )

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
MakeReadOnlyGlobal( "ReduceIntegralRcwaMapping" );

ReduceSemilocalIntegralRcwaMapping := function ( f )

  local  c, m, pi, d_pi, d_piprime, divs, d, cRed, n, i;

  c := f!.coeffs; m := f!.modulus;
  pi := NoninvertiblePrimes(Source(f));
  for n in [1..Length(c)] do
    if c[n][3] < 0 then c[n] := -c[n]; fi;
    d_pi := Gcd(Product(Filtered(Factors(Gcd(NumeratorRat(c[n][1]),
                                             NumeratorRat(c[n][2]))),
                                 p -> p in pi or p = 0)),
                NumeratorRat(c[n][3]));
    d_piprime := c[n][3] / Product(Filtered(Factors(NumeratorRat(c[n][3])),
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
MakeReadOnlyGlobal( "ReduceSemilocalIntegralRcwaMapping" );

ReduceModularRcwaMapping := function ( f )

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
      if   ForAll([1..numresred],
                  i -> Length(Set(csorted{[(i-1)*numresd+1..i*numresd]}))=1)
      then m   := mred;
           deg := deg - degd;
           r   := AllGFqPolynomialsModDegree(q,deg,x);
           c   := csorted{[1, 1 + numresd .. 1 + (numresred-1) * numresd]};
      fi;
    until m <> mred or not IsZero(m mod d);
  od;
  f!.coeffs  := Immutable(c);
  f!.modulus := m;
end;
MakeReadOnlyGlobal( "ReduceModularRcwaMapping" );

CheckClassCycles := function ( R, cycles )

  if not (    ForAll(cycles,IsList)
          and ForAll(Flat(cycles),S->    IsUnionOfResidueClasses(S)
                                     and Length(Residues(S))=1
                                     and IsSubset(R,S)))
     or  ForAny(Combinations(Flat(cycles),2),
                s->Intersection(s[1],s[2]) <> [])
  then Error("there is no rcwa mapping of ",R," having the class ",
             "cycles ",cycles,".\n"); 
  fi;
end;
MakeReadOnlyGlobal( "CheckClassCycles" );

CoeffsOfRcwaMappingByClassCycles := function ( R, cycles )

  local  m, c, res, cyc, pre, im, affectedpos, pos, r1, r2, m1, m2, r, i;

  m   := Lcm(List(Union(cycles),Modulus));
  res := AllResidues(R,m);
  c   := List(res,r->[1,0,1]*One(R));
  for cyc in cycles do
    if Length(cyc) <= 1 then continue; fi;
    for pos in [1..Length(cyc)] do
      pre := cyc[pos]; im := cyc[pos mod Length(cyc) + 1];
      r1 := Residues(pre)[1]; m1 := Modulus(pre);
      r2 := Residues(im )[1]; m2 := Modulus(im);
      affectedpos := Filtered([1..Length(res)],i->res[i] mod m1 = r1);
      for i in affectedpos do c[i] := [m2,m1*r2-m2*r1,m1]; od;
    od;
  od;
  return c;
end;
MakeReadOnlyGlobal( "CoeffsOfRcwaMappingByClassCycles" );

#############################################################################
##
#F  RcwaMappingNC( <coeffs> )
##
InstallOtherMethod( RcwaMappingNC,
                    "integral rcwa mapping by coefficients (RCWA)",
                    true, [ IsList ], 0,

  function ( coeffs )

    local Result;

    if not IsList( coeffs[1] ) or not IsInt( coeffs[1][1] )
    then TryNextMethod( ); fi;
    Result := Objectify( NewType(    IntegralRcwaMappingsFamily,
                                     IsIntegralRcwaMappingInStandardRep ),
                         rec( coeffs  := coeffs,
                              modulus := Length(coeffs) ) );
    SetSource(Result, Integers);
    SetRange (Result, Integers);
    ReduceIntegralRcwaMapping(Result);
    return Result;
  end );

#############################################################################
##
#F  RcwaMapping( <coeffs> )
##
InstallOtherMethod( RcwaMapping,
                    "integral rcwa mapping by coefficients (RCWA)",
                    true, [ IsList ], 0,

  function ( coeffs )

    local quiet;

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
               "integral rcwa mapping.\n");
    fi;
    return RcwaMappingNC( coeffs );
  end );

#############################################################################
##
#F  RcwaMappingNC( <perm>, <range> )
##
InstallOtherMethod( RcwaMappingNC,
                    "integral rcwa mapping by permutation and range (RCWA)",
                    true, [ IsPerm, IsRange ], 0,

  function ( perm, range )

    local coeffs, min, max, m, n, r;

    min := Minimum(range); max := Maximum(range);
    m := max - min + 1; coeffs := [];
    for n in [min..max] do
      r := n mod m + 1;
      coeffs[r] := [1, n^perm - n, 1];
    od;
    return RcwaMappingNC( coeffs );
  end );

#############################################################################
##
#F  RcwaMapping( <perm>, <range> )
##
InstallOtherMethod( RcwaMapping,
                    "integral rcwa mapping by permutation and range (RCWA)",
                    true, [ IsPerm, IsRange ], 0,

  function ( perm, range )

    local quiet;

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
#F  RcwaMappingNC( <modulus>, <values> )
##
InstallOtherMethod( RcwaMappingNC,
                    "integral rcwa mapping by modulus and values (RCWA)",
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
#F  RcwaMapping( <modulus>, <values> )
##
InstallOtherMethod( RcwaMapping,
                    "integral rcwa mapping by modulus and values (RCWA)",
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
         Error("the values ",values," do not define a proper integral ",
               "rcwa mapping.\n"); 
    fi;
    return f;
  end );

#############################################################################
##
#F  RcwaMappingNC( <cycles> )
##
InstallOtherMethod( RcwaMappingNC,
                    "rcwa mapping by class cycles (RCWA)",
                    true, [ IsList ], 0,

  function ( cycles )

    local R, coeffs;

    if not IsUnionOfResidueClasses(cycles[1][1]) then TryNextMethod(); fi;
    R := UnderlyingRing(FamilyObj(cycles[1][1]));
    coeffs := CoeffsOfRcwaMappingByClassCycles(R,cycles);
    if   IsIntegers(R)
    then return RcwaMappingNC(coeffs);
    elif IsZ_pi(R)
    then return RcwaMappingNC(R,coeffs);
    elif IsPolynomialRing(R)
    then return RcwaMappingNC(R,Lcm(List(Flat(cycles),Modulus)),coeffs); fi;
  end );

#############################################################################
##
#F  RcwaMapping( <cycles> )
##
InstallOtherMethod( RcwaMapping,
                    "rcwa mapping by class cycles (RCWA)",
                    true, [ IsList ], 0,

  function ( cycles )

    local R;

    if not IsList(cycles[1]) or
       not IsUnionOfResidueClasses(cycles[1][1])
    then TryNextMethod(); fi;
    R := UnderlyingRing(FamilyObj(cycles[1][1]));
    CheckClassCycles(R,cycles);
    return RcwaMappingNC(cycles);
  end );

#############################################################################
##
#F  RcwaMappingNC( <pi>, <coeffs> )
##
InstallOtherMethod( RcwaMappingNC,
                    "rcwa mapping by prime ideals and coefficients (RCWA)",
                    true, [ IsObject, IsList ], 0,

  function ( pi, coeffs )

    local  f, R, fam;

    if IsInt(pi) then pi := [pi]; fi;
    if   not IsList(pi) or not ForAll(pi,IsInt) or not ForAll(coeffs,IsList)
    then TryNextMethod(); fi;
    R := Z_pi(pi); fam := RcwaMappingsFamily( R );
    f := Objectify( NewType( fam,
                             IsSemilocalIntegralRcwaMappingInStandardRep ),
                    rec( coeffs  := coeffs,
                         modulus := Length(coeffs) ) );
    SetSource(f,R); SetRange(f,R);
    ReduceSemilocalIntegralRcwaMapping(f);
    return f;
  end );

#############################################################################
##
#F  RcwaMapping( <pi>, <coeffs> )
##
InstallOtherMethod( RcwaMapping,
                    "rcwa mapping by prime ideals and coefficients (RCWA)",
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
               pi," - semilocal integral rcwa mapping.\n");
    fi;
    return RcwaMappingNC(pi,coeffs);
  end );

#############################################################################
##
#F  RcwaMappingNC( <q>, <modulus>, <coeffs> )
##
InstallOtherMethod( RcwaMappingNC,
                    "rcwa mapping by prime ideals and coefficients (RCWA)",
                    true, [ IsInt, IsPolynomial, IsList ], 0,

  function ( q, modulus, coeffs )

    local  f, R, fam, ind;

    ind := IndeterminateNumberOfLaurentPolynomial( coeffs[1][1] );
    R   := PolynomialRing( GF( q ), [ ind ] );
    fam := RcwaMappingsFamily( R );
    f   := Objectify( NewType( fam, IsModularRcwaMappingInStandardRep ),
                      rec( coeffs  := coeffs,
                           modulus := modulus ) );
    SetUnderlyingField( f, CoefficientsRing( R ) );
    SetSource( f, R ); SetRange( f, R );
    ReduceModularRcwaMapping( f );
    return f;
  end );

#############################################################################
##
#F  RcwaMapping( <q>, <modulus>, <coeffs> )
##
InstallOtherMethod( RcwaMapping,
                    "rcwa mapping by prime ideals and coefficients (RCWA)",
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
#F  RcwaMappingNC( <R>, <coeffs> )
##
InstallOtherMethod( RcwaMappingNC,
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
#F  RcwaMapping( <R>, <coeffs> )
##
InstallOtherMethod( RcwaMapping,
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
#F  RcwaMappingNC( <R>, <modulus>, <coeffs> )
##
InstallOtherMethod( RcwaMappingNC,
                    "rcwa mapping by ring, modulus and coefficients (RCWA)",
                    ReturnTrue, [ IsRing, IsRingElement, IsList ], 0,

  function ( R, modulus, coeffs )

    if not modulus in R then TryNextMethod(); fi;
    if   IsIntegers(R) or IsZ_pi(R)
    then return RcwaMappingNC(R,coeffs);
    elif IsPolynomialRing(R)
    then return RcwaMappingNC(Size(UnderlyingField(R)),modulus,coeffs);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#F  RcwaMapping( <R>, <modulus>, <coeffs> )
##
InstallOtherMethod( RcwaMapping,
                    "rcwa mapping by ring, modulus and coefficients (RCWA)",
                    ReturnTrue, [ IsRing, IsRingElement, IsList ], 0,

  function ( R, modulus, coeffs )

    if not modulus in R then TryNextMethod(); fi;
    if   IsIntegers(R) or IsZ_pi(R)
    then return RcwaMapping(R,coeffs);
    elif IsPolynomialRing(R)
    then return RcwaMapping(Size(UnderlyingField(R)),modulus,coeffs);
    else TryNextMethod(); fi;
  end );

IdChars := function ( n, ch )
  return Concatenation( ListWithIdenticalEntries( n, ch ) );
end;
MakeReadOnlyGlobal( "IdChars" );

DisplayIntegralAffineMapping := function ( t )

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
MakeReadOnlyGlobal( "DisplayIntegralAffineMapping" );

DisplaySemilocalIntegralAffineMapping := function ( t )

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
MakeReadOnlyGlobal( "DisplaySemilocalIntegralAffineMapping" );

DisplayModularAffineMapping := function ( t, maxlng )

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
  elif b = zero then if   not a in [-one,one] then append(factorstr(a),"*P");
                     elif a = one then append("P"); else append("-P"); fi;
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
MakeReadOnlyGlobal( "DisplayModularAffineMapping" );

LaTeXIntegralAffineMapping := function ( t )

  local  str, a, b, c, append;
 
  append := function ( arg )
    str := CallFuncList(Concatenation,
                        Concatenation([str],List(arg,String)));
  end;

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
  elif b = 0 then append("\\frac{");
                  if   AbsInt(a) <> 1 then append(a);
                  elif a = -1         then append("-");
                  fi;
                  append("n}{",c,"}");
  else append("\\frac{");
       if   AbsInt(a) <> 1 then append(a);
       elif a = -1         then append("-");
       fi;
       append("n");
       if   b > 0 then append(" + ", b);
       elif b < 0 then append(" - ",-b);
       fi;
       append("}{",c,"}");
  fi;
  return str;
end;
MakeReadOnlyGlobal( "LaTeXIntegralAffineMapping" );

#############################################################################
##
#M  String( <f> ) . . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( String,
               "for integral rcwa mappings (RCWA)", true,
               [ IsIntegralRcwaMappingInStandardRep ], 0,

  function ( arg )

    local f, lng, s;

    f := arg[1]; if Length(arg) > 1 then lng := arg[2]; fi;
    s := Concatenation( "RcwaMapping( ", String( f!.coeffs ), " )" );
    if IsBound(lng) then s := String(s,lng); fi;
    return s;
  end );

#############################################################################
##
#M  String( <f> ) . . . . . . . . . . . . for semilocal integral rcwa mapping
##
InstallMethod( String,
               "for semilocal integral rcwa mappings (RCWA)",
               true, [ IsSemilocalIntegralRcwaMappingInStandardRep ], 0,

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
#M  String( <f> ) . . . . . . . . . . . . . . . . .  for modular rcwa mapping
##
InstallMethod( String,
               "for modular rcwa mappings (RCWA)",
               true, [ IsModularRcwaMappingInStandardRep ], 0,

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
#M  PrintObj( <f> ) . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( PrintObj,
               "for integral rcwa mappings (RCWA)", true,
               [ IsIntegralRcwaMappingInStandardRep ], SUM_FLAGS,

  function ( f )
    Print( "RcwaMapping( ", f!.coeffs, " )" );
  end );

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . for semilocal integral rcwa mapping
##
InstallMethod( PrintObj,
               "for semilocal integral rcwa mappings (RCWA)", true,
               [ IsSemilocalIntegralRcwaMappingInStandardRep ],  SUM_FLAGS,

  function ( f )
    Print( "RcwaMapping( ",
           NoninvertiblePrimes(Source(f)), ", ", f!.coeffs, " )" );
  end );

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . . . . . .  for modular rcwa mapping
##
InstallMethod( PrintObj,
               "for modular rcwa mappings (RCWA)", true,
               [ IsModularRcwaMappingInStandardRep ], SUM_FLAGS,

  function ( f )
    Print( "RcwaMapping( ", Size(UnderlyingField(f)),
           ", ", f!.modulus, ", ", f!.coeffs, " )" );
  end );

#############################################################################
##
#M  ViewObj( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
InstallMethod( ViewObj,
               "for rational-based and modular rcwa mappings (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )

    if IsZero(f) or IsOne(f) then View(f); return; fi;
    if IsOne(Modulus(f)) then Display(f:NoLineFeed); return; fi;
    if not IsRcwaMappingStandardRep(f) then TryNextMethod(); fi;
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
#M  Display( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
##  Display the rcwa mapping <f> as a nice, human-readable table.
##
InstallMethod( Display,
               "for rational-based and modular rcwa mappings (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,

  function ( f )

    local  m, c, pi, q, d, x, RingString, name, VarName,
           r, NrResidues, poses, pos, t, i, scr, l1, l2, l3, str,
           mdec, mstr, MaxPolLng, FlushLng, prefix;

    if not IsRcwaMappingStandardRep(f) then TryNextMethod(); fi;
    m := f!.modulus; c := f!.coeffs;
    if HasName(f) then name := Name(f); else name := "f"; fi;
    prefix := false; RingString := RingToString(Source(f));
    if   IsModularRcwaMapping(f)
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
           if   IsIntegralRcwaMapping(f)
           then DisplayIntegralAffineMapping(c[1]);
           elif IsSemilocalIntegralRcwaMapping(f)
           then DisplaySemilocalIntegralAffineMapping(c[1]);
           else DisplayModularAffineMapping(c[1],SizeScreen()[1]-48); fi;
         else
           Print(" with modulus ",m);
           if   HasOrder(f) and not (HasIsTame(f) and not IsTame(f))
           then Print(", of order ",Order(f)); fi;
           Print("\n\n");
           scr := SizeScreen()[1] - 2;
           if   IsRationalBasedRcwaMapping(f)
           then l1 := Int(scr/2); else l1 := Int(scr/3); fi;
           mstr := String(m);
           if l1 - Length(mstr) - 6 <= 0 then mstr := "<modulus>"; fi;
           mdec := Length(mstr);
           l2 := Int((l1 - mdec - 6)/2);
           l3 := Int((scr - l1 - Length(name) - 3)/2);
           if   IsRationalBasedRcwaMapping(f)
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
               if   IsRationalBasedRcwaMapping(f)
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
             if   IsIntegralRcwaMapping(f)
             then DisplayIntegralAffineMapping(c[pos[1]+1]);
             elif IsSemilocalIntegralRcwaMapping(f)
             then DisplaySemilocalIntegralAffineMapping(c[pos[1]+1]);
             else DisplayModularAffineMapping(c[pos[1]+1],scr-l1-4); fi;
           od;
           Print("\n");
         fi;
    fi;
    if ValueOption("NoLineFeed") <> true then Print("\n"); fi;
  end );

#############################################################################
##
#M  LaTeXObj( <f> ) . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( LaTeXObj,
               "for integral rcwa mappings (RCWA)", true,
               [ IsIntegralRcwaMapping ], 0,

  function ( f )

    local  c, m, mred, str, affs, maxafflng, t, poses, pos, res,
           indent, append, i, j;

    append := function ( arg )
      str := CallFuncList(Concatenation,
                          Concatenation([str],List(arg,String)));
    end;

    c := Coefficients(f); m := Length(c);
    if m = 1 then
      return Concatenation("n \\ \\mapsto \\ ",
                           LaTeXIntegralAffineMapping(c[1]));
    fi;
    indent := ValueOption("Indentation");
    if not IsPosInt(indent)
    then indent := ""; else indent := String(" ",indent); fi;
    str := indent;
    append("n \\ \\longmapsto \\\n",indent,"\\begin{cases}\n");
    poses := AsSortedList( List( Set(c),
                                 t -> Filtered( [0..m-1],
                                                i -> c[i+1] = t ) ) );
    affs := List( c, LaTeXIntegralAffineMapping );
    maxafflng := Maximum( List( affs, Length ) );
    for pos in poses do
      append( indent, "  ", affs[ pos[1] + 1 ],
              String( " ", maxafflng - Length( affs[pos[1]+1] ) + 1 ) );
      append(" & \\text{if} \\ n \\equiv ");
      mred := Minimum( Filtered( DivisorsInt(m),
                                 d -> ForAll(Collected(List(pos,j->j mod d)),
                                             t -> t[2] = m/d) ) );
      res := Set( List( pos, j -> j mod mred ) );
      for i in res do
        append(i);
        if i <> res[Length(res)] then append(", "); fi;
      od;
      append(" \\ (",mred,")");
      if   pos = poses[ Length(poses) ]
      then append(".\n");
      else append(", \\\\\n"); fi;
    od;
    append(indent,"\\end{cases}\n");
    return str;
  end );

#############################################################################
##
#M  \=( <f>, <g> ) . . . . . . . . . . . . for "rational-based" rcwa mappings
##
InstallMethod( \=,
               "for two rational-based rcwa mappings (RCWA)",
               IsIdenticalObj,
               [ IsRationalBasedRcwaMappingInStandardRep,
                 IsRationalBasedRcwaMappingInStandardRep ], 0,

  function ( f, g )
    return f!.coeffs = g!.coeffs;
  end );

#############################################################################
##
#M  \=( <f>, <g> ) . . . . . . . . . . . . . . . .  for modular rcwa mappings
##
InstallMethod( \=,
               "for two modular rcwa mappings (RCWA)",
               IsIdenticalObj,
               [ IsModularRcwaMappingInStandardRep,
                 IsModularRcwaMappingInStandardRep ], 0,

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
#V  ZeroIntegralRcwaMapping . . . . . . . . . . .  zero integral rcwa mapping
##
InstallValue( ZeroIntegralRcwaMapping, RcwaMapping( [ [ 0, 0, 1 ] ] ) );
SetIsZero( ZeroIntegralRcwaMapping, true );

#############################################################################
##
#V  IdentityIntegralRcwaMapping . . . . . . .  identity integral rcwa mapping
##
InstallValue( IdentityIntegralRcwaMapping, RcwaMapping( [ [ 1, 0, 1 ] ] ) );
SetIsOne( IdentityIntegralRcwaMapping, true );

#############################################################################
##
#M  ZeroOp( <f> ) . . . . . . . . . . . . . . . . . for integral rcwa mapping
##
##  Zero rcwa mapping.
##
InstallMethod( ZeroOp,
               "for integral rcwa mappings (RCWA)", true,
               [ IsIntegralRcwaMappingInStandardRep ], 0,
               f -> ZeroIntegralRcwaMapping );

#############################################################################
##
#M  ZeroOp( <f> ) . . . . . . . . . . . . for semilocal integral rcwa mapping
##
##  Zero rcwa mapping.
##
InstallMethod( ZeroOp,
               "for semilocal integral rcwa mappings (RCWA)",
               true, [ IsSemilocalIntegralRcwaMappingInStandardRep ], 0,

  function ( f )

    local  zero;

    zero := RcwaMappingNC( NoninvertiblePrimes(Source(f)), [[0,0,1]] );
    SetIsZero( zero, true ); return zero;
  end );

#############################################################################
##
#M  ZeroOp( <f> ) . . . . . . . . . . . . . . . . .  for modular rcwa mapping
##
##  Zero rcwa mapping.
##
InstallMethod( ZeroOp,
               "for modular rcwa mappings (RCWA)",
               true, [ IsModularRcwaMappingInStandardRep ], 0,

  function ( f )

    local  zero;

    zero := RcwaMappingNC( Size(UnderlyingField(f)), One(Source(f)),
                           [[0,0,1]] * One(Source(f)) );
    SetIsZero( zero, true ); return zero;
  end );

#############################################################################
## 
#M  IsZero( <f> ) . . . . . . . . . . . . . . . . . . . . .  for rcwa mapping
## 
##  <f> = zero rcwa mapping ? 
## 
InstallMethod( IsZero,
               "for rcwa mappings (RCWA)", true,
               [ IsRcwaMappingInStandardRep ], 0,
               f -> f!.coeffs = [ [ 0, 0, 1 ] ] * One( Source( f ) ) );  

#############################################################################
##
#M  OneOp( <f> ) . . . . . . . . . . . . . . . . .  for integral rcwa mapping
##
##  Identity rcwa mapping.
##
InstallMethod( OneOp,
               "for integral rcwa mappings (RCWA)", true,
               [ IsIntegralRcwaMappingInStandardRep ], 0,
               f -> IdentityIntegralRcwaMapping );

#############################################################################
##
#M  OneOp( <f> ) . . . . . . . . . . . .  for semilocal integral rcwa mapping
##
##  Identity rcwa mapping.
##
InstallMethod( OneOp,
               "for semilocal integral rcwa mappings (RCWA)",
               true, [ IsSemilocalIntegralRcwaMappingInStandardRep ], 0,

  function ( f )

    local  one;

    one := RcwaMappingNC( NoninvertiblePrimes(Source(f)), [[1,0,1]] );
    SetIsOne( one, true ); return one;
  end );


#############################################################################
##
#M  OneOp( <f> ) . . . . . . . . . . . . . . . . . . for modular rcwa mapping
##
##  Identity rcwa mapping.
##
InstallMethod( OneOp,
               "for modular rcwa mappings (RCWA)",
               true, [ IsModularRcwaMappingInStandardRep ], 0,

  function ( f )

    local  one;
 
    one := RcwaMappingNC( Size(UnderlyingField(f)), One(Source(f)),
                          [[1,0,1]] * One(Source(f)) );
    SetIsOne( one, true ); return one;
  end );

#############################################################################
## 
#M  IsOne( <f> ) . . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
## 
##  <f> = identity rcwa mapping ? 
## 
InstallMethod( IsOne, 
               "for rcwa mappings (RCWA)", true,
               [ IsRcwaMappingInStandardRep ], 0,
               f -> f!.coeffs = [ [ 1, 0, 1 ] ] * One( Source( f ) ) );  

#############################################################################
##
#M  Coefficients( <f> ) . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
InstallOtherMethod( Coefficients,
                    "for rcwa mappings (RCWA)", true,
                    [ IsRcwaMappingInStandardRep ], 0, f -> f!.coeffs );

#############################################################################
##
#M  Modulus( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
InstallMethod( Modulus,
               "for rcwa mappings (RCWA)", true,
               [ IsRcwaMappingInStandardRep ], 0, f -> f!.modulus );

#############################################################################
##
#M  Multiplier( <f> ) . . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
InstallMethod( Multiplier,
               "for rcwa mappings (RCWA)", true,
               [ IsRcwaMappingInStandardRep ], 0,
               f -> Lcm( List( f!.coeffs, c -> c[1] ) ) );

#############################################################################
##
#M  Multiplier( <f> ) . . . . . . . . . . for semilocal integral rcwa mapping
##
InstallMethod( Multiplier,
               "for semilocal integral rcwa mappings (RCWA)",
               true, [ IsSemilocalIntegralRcwaMappingInStandardRep ], 10,


  f -> Lcm( List( f!.coeffs,
                  c -> StandardAssociate( Source( f ), c[1] ) ) ) );

#############################################################################
##
#M  Divisor( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
InstallMethod( Divisor,
               "for rcwa mappings (RCWA)",
               true, [ IsRcwaMappingInStandardRep ], 0,
               f -> Lcm( List( f!.coeffs, c -> c[ 3 ] ) ) );

#############################################################################
##
#M  Multpk( <f>, <p>, <k> ) . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( Multpk,
               "for integral rcwa mappings (RCWA)",
               true, [ IsIntegralRcwaMapping, IsInt, IsInt ], 0,

  function ( f, p, k )

    local  m, c, res;

    m := Modulus(f); c := Coefficients(f);
    if k > 0
    then res := Filtered([0..m-1],r ->     c[r+1][1] mod p^k=0
                                       and c[r+1][1] mod p^(k+1)<>0);
    elif k < 0
    then res := Filtered([0..m-1],r ->     c[r+1][3] mod p^(-k)=0
                                       and c[r+1][3] mod p^(-k+1)<>0);
    else res := Filtered([0..m-1],r ->     c[r+1][1] mod p<>0
                                       and c[r+1][3] mod p<>0);
    fi;
    return ResidueClassUnion(Integers,m,res);
  end );

#############################################################################
##
#M  IsIntegral( <f> ) . . . . . . . . . . . . . . . .. . . . for rcwa mapping
##
InstallMethod( IsIntegral,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               f -> IsOne( Divisor( f ) ) );

#############################################################################
##
#M  IsBalanced( <f> ) . . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
InstallMethod( IsBalanced,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  f -> Set( Factors( Multiplier( f ) ) ) = Set( Factors( Divisor( f ) ) ) );

#############################################################################
##
#M  IsClassWiseOrderPreserving( <f> ) . . . for "rational-based" rcwa mapping
##
InstallMethod( IsClassWiseOrderPreserving,
               "for rational-based rcwa mappings (RCWA)",
               true, [ IsRationalBasedRcwaMappingInStandardRep ], 0,
               f -> ForAll( f!.coeffs, c -> c[ 1 ] >= 0 ) );

#############################################################################
##
#M  MovedPoints( <f> ) . . . . . . . . . . . . . . for bijective rcwa mapping
##
##  The set of moved points (support) of the bijective rcwa mapping <f>.
##
InstallOtherMethod( MovedPoints,
                    "for bijective rcwa mapping (RCWA)", true,
                    [ IsRcwaMapping ], 0,

  function ( f )

    local  m, c, R, q, d, x, r, pols, residues, fixed, fixpoint;

    if not IsBijective(f) then TryNextMethod(); fi;
    m := Modulus(f); c := Coefficients(f); R := Source(f);
    if   IsRationalBasedRcwaMapping(f)
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
    if IsModularRcwaMapping(f) then residues := pols{residues+1}; fi;
    return ResidueClassUnion(R,m,residues,[],fixed);
  end );

#############################################################################
##
#M  ImageElm( <f>, <n> ) . . . . . . .  for integral rcwa mapping and integer
##
##  Image of the integer <n> under the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "for integral rcwa mapping and integer (RCWA)",
               true, [ IsIntegralRcwaMappingInStandardRep, IsInt ], 0,

  function ( f, n )

    local  m, c;

    m := f!.modulus; c := f!.coeffs[n mod m + 1];
    return (c[1] * n + c[2]) / c[3];
  end );

#############################################################################
##
#M  ImageElm( <f>, <n> ) . . for semilocal int. rcwa mapping and Z_pi-element
##
##  Image of the element <n> of the ring $\Z_{(\pi)}$ for suitable <pi> under
##  the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "for semilocal integral rcwa mapping and el. of Z_pi (RCWA)",
               true, [ IsSemilocalIntegralRcwaMappingInStandardRep, IsRat ],
               0,

  function ( f, n )

    local  m, c;

    if not n in Source(f) then TryNextMethod(); fi;
    m := f!.modulus; c := f!.coeffs[n mod m + 1];
    return (c[1] * n + c[2]) / c[3];
  end );

#############################################################################
##
#M  ImageElm( <f>, <p> ) . . . . . .  for modular rcwa mapping and polynomial
##
##  Image of the polynomial <p> under the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "for modular rcwa mapping and polynomial (RCWA)",
               true, [ IsModularRcwaMappingInStandardRep, IsPolynomial ], 0,

  function ( f, p )

    local  R, m, c, r;

    R := Source(f); if not p in R then TryNextMethod(); fi;
    m := f!.modulus; r := p mod m;
    c := f!.coeffs[PositionSorted(AllResidues(R,m),r)];
    return (c[1] * p + c[2]) / c[3];
  end );

#############################################################################
##
#M  \^( <n>, <f> ) . . . . . . . . . . . .  for ring element and rcwa mapping
##
##  Image of the ring element <n> under the rcwa mapping <f>. 
##
InstallMethod( \^,
               "for ring element and rcwa mapping (RCWA)",
               ReturnTrue, [ IsRingElement, IsRcwaMapping ], 0,

  function ( n, f )
    return ImageElm( f, n );
  end );

#############################################################################
##
#M  ImagesElm( <f>, <n> ) . . . . . . . . . for rcwa mapping and ring element
##
##  Images of the ring element <n> under the rcwa mapping <f>.
##  For technical purposes, only.
##
InstallMethod( ImagesElm,
               "for rcwa mapping and ring element (RCWA)",
               true, [ IsRcwaMapping, IsRingElement ], 0,

  function ( f, n )
    return [ ImageElm( f, n ) ];
  end ); 

#############################################################################
##
#M  ImagesSet( <f>, <S> ) . . . for rcwa mapping and union of residue classes
##
##  Image of the set <S> under the rcwa mapping <f>.
##
InstallOtherMethod( ImagesSet,
                    "for rcwa mapping and residue class union (RCWA)",
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
#M  \^( <S>, <f> ) . . . . . . . . . . . . . . . . . for set and rcwa mapping
##
##  Image of the set <S> under the rcwa mapping <f>.
##  In particular, <S> can be a union of residue classes.
##
InstallOtherMethod( \^,
                    "for set and rcwa mapping (RCWA)",
                    ReturnTrue, [ IsListOrCollection, IsRcwaMapping ], 0,

  function ( S, f )
    return ImagesSet( f, S );
  end );

#############################################################################
##
#M  PreImageElm( <f>, <n> ) . . . for bijective rcwa mapping and ring element
##
##  Preimage of the ring element <n> under the bijective rcwa mapping <f>.
##
InstallMethod( PreImageElm,
               "for bijective rcwa mapping and ring element (RCWA)",
               true, [ IsRcwaMapping and IsBijective, IsRingElement ], 0,

  function ( f, n )
    return n^Inverse( f );
  end );

#############################################################################
##
#M  PreImagesElm( <f>, <n> ) . . . . .  for integral rcwa mapping and integer
##
##  Preimages of the integer <n> under the rcwa mapping <f>. 
##
InstallMethod( PreImagesElm,
               "for integral rcwa mapping and integer (RCWA)", true, 
               [ IsIntegralRcwaMappingInStandardRep, IsInt ], 0,

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
#M  PreImagesRepresentative( <f>, <n> ) . . for int. rcwa mapping and integer
##
##  A representative of the set of preimages of the integer <n> under the
##  integral rcwa mapping <f>. 
##
InstallMethod( PreImagesRepresentative,
               "for integral rcwa mapping and integer (RCWA)", true, 
               [ IsIntegralRcwaMappingInStandardRep, IsInt ], 0,

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
#M  PreImagesSet( <f>, <R> ) . . . . . . for rcwa mapping and underlying ring
##
##  Preimage of the rcwa mapping <f>. For technical purposes, only.
##
InstallMethod( PreImagesSet,
               "for rcwa mapping and underlying ring (RCWA)", true, 
               [ IsRcwaMapping, IsRing ], 0,

  function ( f, R )
    if   R = UnderlyingRing( FamilyObj( f ) )
    then return R; else TryNextMethod( ); fi;
  end );

#############################################################################
##
#M  PreImagesSet( <f>, <l> ) . for rcwa mapping and list of el's of its range
##
InstallOtherMethod( PreImagesSet,
                    "for rcwa map. and list of elements of its range (RCWA)",
                    true, [ IsRcwaMapping, IsList ], 0,

  function ( f, l )
    return Union( List( Set( l ), n -> PreImagesElm( f, n ) ) );
  end );

#############################################################################
##
#M  PreImagesSet( <f>, <S> ) . . for integral rcwa map. and union of res. cl.
##
##  Preimage of the set <S> under the rcwa mapping <f>.
##
InstallMethod( PreImagesSet,
               "for integral rcwa mapping and residue class union (RCWA)",
               true, [ IsIntegralRcwaMapping, IsUnionOfResidueClassesOfZ ],
               0,

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
#M  \+( <f>, <g> ) . . . . . . . . . . . for two rational-based rcwa mappings
##
##  Pointwise sum of the rcwa mappings <f> and <g>.
##
InstallMethod( \+,
               "for two rational-based rcwa mappings (RCWA)",
               IsIdenticalObj,
               [ IsRationalBasedRcwaMappingInStandardRep,
                 IsRationalBasedRcwaMappingInStandardRep ], 0,

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

    if   IsIntegralRcwaMapping( f )
    then return RcwaMappingNC( c3 );
    else pi := NoninvertiblePrimes( Source( f ) );
         return RcwaMappingNC( pi, c3 );
    fi;
  end );

#############################################################################
##
#M  \+( <f>, <g> ) . . . . . . . . . . . . . .  for two modular rcwa mappings
##
##  Pointwise sum of the rcwa mappings <f> and <g>.
##
InstallMethod( \+,
               "for two modular rcwa mappings (RCWA)",
               IsIdenticalObj,
               [ IsModularRcwaMappingInStandardRep,
                 IsModularRcwaMappingInStandardRep ], 0,

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
#M  AdditiveInverseOp( <f> ) . . . . . . . . . . . . . . . . for rcwa mapping
##
##  Pointwise additive inverse of rcwa mapping <f>.
##
InstallMethod( AdditiveInverseOp,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               f -> f * RcwaMappingNC( Source(f), One(Source(f)),
                                       [[-1,0,1]] * One(Source(f)) ) );

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . .  for two rational-based rcwa mappings
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for two rational-based rcwa mappings (RCWA)",
               IsIdenticalObj,
               [ IsRationalBasedRcwaMappingInStandardRep,
                 IsRationalBasedRcwaMappingInStandardRep ], SUM_FLAGS,

  function ( g, f )

    local  fg, c1, c2, c3, m1, m2, m3, n, n1, n2, pi;

    c1 := f!.coeffs;  c2 := g!.coeffs;
    m1 := f!.modulus; m2 := g!.modulus;
    m3 := Minimum( Lcm( m1, m2 ) * Divisor( f ), m1 * m2 );

    c3 := [];
    for n in [0 .. m3 - 1] do
      n1 := n mod m1 + 1;
      n2 := (c1[n1][1] * n + c1[n1][2])/c1[n1][3] mod m2 + 1;
      Add(c3, [ c1[n1][1] * c2[n2][1],
                c1[n1][2] * c2[n2][1] + c1[n1][3] * c2[n2][2],
                c1[n1][3] * c2[n2][3] ]);
    od;

    if   IsIntegralRcwaMapping(f) 
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
#M  CompositionMapping2( <g>, <f> ) . . . . . . for two modular rcwa mappings
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for two modular rcwa mappings (RCWA)",
               IsIdenticalObj,
               [ IsModularRcwaMappingInStandardRep,
                 IsModularRcwaMappingInStandardRep ], SUM_FLAGS,

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
#M  InverseOp( <f> ) . . . . . . . . . . . .  for rational-based rcwa mapping
##
##  Inverse mapping of bijective rcwa mapping <f>.
##
InstallMethod( InverseOp,
               "for rational-based rcwa mappings (RCWA)", true,
               [ IsRationalBasedRcwaMappingInStandardRep ], 0,
               
  function ( f )

    local  Result, c, cInv, m, mInv, n, t, tm, tn, Classes, cl, pi;

    c := f!.coeffs; m := f!.modulus;
    cInv := [];
    mInv := Multiplier( f ) * m / Gcd( m, Gcd( List( c, t -> t[3] ) ) );
    for n in [ 1 .. m ] do
      t := [c[n][3], -c[n][2], c[n][1]]; if t[3] = 0 then return fail; fi;
      tm := StandardAssociate(Source(f),c[n][1]) * m / Gcd(m,c[n][3]);
      tn := ((n - 1) * c[n][1] + c[n][2]) / c[n][3] mod tm;
      Classes := List([1 .. mInv/tm], i -> (i - 1) * tm + tn);
      for cl in Classes do
        if IsBound(cInv[cl + 1]) and cInv[cl + 1] <> t then return fail; fi; 
        cInv[cl + 1] := t;
      od;
    od;

    if not ForAll([1..mInv], i -> IsBound(cInv[i])) then return fail; fi;

    if   IsIntegralRcwaMapping( f )
    then Result := RcwaMappingNC( cInv );
    else pi := NoninvertiblePrimes( Source( f ) );
         Result := RcwaMappingNC( pi, cInv );
    fi;
    SetInverse(f, Result); SetInverse(Result, f);
    if HasOrder(f) then SetOrder(Result, Order(f)); fi;

    return Result;
  end );

#############################################################################
##
#M  InverseOp( <f> ) . . . . . . . . . . . . . . . . for modular rcwa mapping
##
##  Inverse mapping of bijective rcwa mapping <f>.
##
InstallMethod( InverseOp,
               "for modular rcwa mappings (RCWA)", true,
               [ IsModularRcwaMappingInStandardRep ], 0,
               
  function ( f )

    local  Result, c, cInv, m, mInv, d, dInv, R, q, x,
           respols, res, resInv, r, n, t, tm, tr, tn, Classes, cl, pos;

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
      tm := StandardAssociate(Source(f),c[n][1]) * m / Gcd(m,c[n][3]);
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
    SetInverse(f, Result); SetInverse(Result, f);
    if HasOrder(f) then SetOrder(Result, Order(f)); fi;

    return Result;
  end );

#############################################################################
##
#M  InverseGeneralMapping( <f> ) . . . . . . . . . . . . . . for rcwa mapping
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
#M  \^( <g>, <h> ) . . . . . . . . . . . . . . . . . .  for two rcwa mappings
##
##  Conjugate of the rcwa mapping <g> under <h>.
##
InstallMethod( \^,
               "for two rcwa mappings (RCWA)",
               IsIdenticalObj, [ IsRcwaMapping, IsRcwaMapping ], 0,

  function ( g, h )

    local  f;

    f := h^-1 * g * h;
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
#M  \^( <f>, <n> ) . . . . . . . . . . . . . . . for rcwa mapping and integer
##
##  <n>-th power of the rcwa mapping <f>. 
##  This method is for faster handling of the case of a negative exponent
##  if the inverse of <f> already has been computed.
##
InstallMethod( \^,
               "for rcwa mapping and integer (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsInt ], 0,

  function ( f, n )

    local  pow;

    if ValueOption("UseKernelPOW") = true then TryNextMethod(); fi;

    if   n = 0 then return One( f );
    elif n = 1 then return f;
    elif n > 1 then pow := POW(f,n:UseKernelPOW);
               else pow := POW(Inverse( f ),-n:UseKernelPOW);
    fi;

    if HasIsTame(f) then SetIsTame(pow,IsTame(f)); fi;

    if HasOrder(f) then
      if Order(f) = infinity then SetOrder(pow,infinity); else
        SetOrder(pow,Order(f)/Gcd(Order(f),n));
      fi;
    fi;

    return pow;
  end );

#############################################################################
##
#M  IsInjective( <f> ) . . . . . . . . . . .  for rational-based rcwa mapping
##
InstallMethod( IsInjective,
               "for rational-based rcwa mappings (RCWA)", true,
               [ IsRationalBasedRcwaMappingInStandardRep ], 0,

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
#M  IsInjective( <f> ) . . . . . . . . . . . . . . . for modular rcwa mapping
##
InstallMethod( IsInjective,
               "for modular rcwa mappings (RCWA)", true,
               [ IsModularRcwaMappingInStandardRep ], 0,

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
#M  IsSurjective( <f> ) . . . . . . . . . . . for rational-based rcwa mapping
##
InstallMethod( IsSurjective,
               "for rational-based rcwa mappings (RCWA)", true,
               [ IsRationalBasedRcwaMappingInStandardRep ], 0, 

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
#M  IsSurjective( <f> ) . . . . . . . . . . . . . .  for modular rcwa mapping
##
InstallMethod( IsSurjective,
               "for modular rcwa mappings (RCWA)", true,
               [ IsModularRcwaMappingInStandardRep ], 0,
               
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

#############################################################################
##
#M  IsUnit( <f> ) . . . . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
InstallOtherMethod( IsUnit,
                    "for rcwa mappings (RCWA)",
                    true, [ IsRcwaMapping ], 0, IsBijective );

#############################################################################
##
#M  Order( <f> ) . . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
##  The `factors of multiplier and divisor' criterion.
##
InstallMethod( Order,
               "for rcwa mappings, factors of mult. and div. - crit. (RCWA)",
               true, [ IsRcwaMapping ], 50,

  function ( f )

    local  R, mult, div;

    if not IsBijective(f) then TryNextMethod(); fi;
    R := Source(f); mult := Multiplier(f); div := Divisor(f);
    if Set(Factors(R,mult)) <> Set(Factors(R,div))
    then return infinity; else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  Order( <f> ) . . . . . . . . . . . . . .  for rational-based rcwa mapping
##
##  This method tests whether <f> satisfies one sufficient criterium for
##  having infinite order: it checks whether there is a small, smooth
##  exponent <e> such that <f>^<e> maps one residue class mod. the modulus
##  non-identically onto itself; in case <f> does not, it gives up.
##
InstallMethod( Order,
               "for rat.-based rcwa map's, arith. progression method (RCWA)",
               true, [ IsRationalBasedRcwaMappingInStandardRep ], 20,

  function ( f )

    local  g, c, m1, m2, exp, e, n, r, one;

    one := One(f);
    if f = one then return 1; fi;
    if not IsBijective(f) 
    then Error("Order: <rcwa mapping> must be bijective"); fi;
    m1 := f!.modulus; g := f;
    exp := [2,2,3,5,2,7,3,2,11,13,5,3,17,19,2]; e := 1;
    for n in exp do
      c := g!.coeffs; m2 := g!.modulus;
      if m2 > m1 or IsOne(g) then TryNextMethod(); fi;
      r := First([1..m2], n ->     c[n] <> [1,0,1] and c[n]{[1,3]} = [1,1]
                               and c[n][2] mod m2 = 0);
      if   r <> fail
      then Info(InfoRCWA,1,"Order: the ",Ordinal(e)," power of the argument",
                           " is ",g,"; this mapping maps the residue ",
                           "class ",r-1,"(",m2,") non-identically ",
                           "onto itself, hence its order is infinity.");
           return infinity;
      fi;
      g := g^n; e := e * n; if g = one then break; fi;
    od;
    TryNextMethod();
  end );

#############################################################################
##
#M  Order( <f> ) . . . . . . . . . . . . . . . . .  for integral rcwa mapping
##
##  This method tries to enumerate cycles of the rcwa mapping <f>.
##  In case <f> has finite order, it may determine it or give up.
##  It also checks whether <f> has a cycle whose length exceeds two times
##  the square of the modulus, and returns `infinity', if so.
##  The validity of this probably sufficient criterium for <f> having
##  infinite order has not yet been proved.
##
InstallMethod( Order,
               "for integral rcwa mappings, cycle method (RCWA)",
               true, [ IsIntegralRcwaMapping ], 0,

  function ( f )

    local  MaxFiniteCycleLength, CycLng, CycLngs, one, n, m, i;

    one := One(f); 
    if f = one then return 1; fi;
    if not IsBijective(f) 
    then Error("Order: <rcwa mapping> must be bijective"); fi;
    MaxFiniteCycleLength := 2 * Modulus(f)^2;
    for i in [1..10] do  # 10 trials ...
      n := Random([1..2^27]); m := n; CycLng := 0; CycLngs := [];
      repeat
        m := m^f; CycLng := CycLng + 1;
      until m = n or CycLng > MaxFiniteCycleLength;
      if CycLng > MaxFiniteCycleLength then
        Info(InfoRCWA,1,"Order: the mapping ",f," has a cycle longer than ",
                        "2 times the square of its modulus, hence we claim ",
                        "its order is infinity, although the validity of ",
                        "this criterium has not been proved so far.");
        return infinity;
      fi;
      Add(CycLngs,CycLng);
    od;
    if f^Lcm(CycLngs) = one 
    then return Lcm(CycLngs); else TryNextMethod(); fi;
  end );

#############################################################################
##
#F  TransitionMatrix( <f>, <m> ) . . transition matrix of <f> for modulus <m>
##
InstallGlobalFunction( TransitionMatrix,

  function ( f, m )

    local  T, R, mTest, Resm, ResmTest, n, i, j;

    if not IsRcwaMapping(f) or not m in Source(f) then
      Error("usage: TransitionMatrix( <f>, <m> ),\nwhere <f> is an ",
            "rcwa mapping and <m> lies in the source of <f>.\n");
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
#M  TransitionGraph( <f>, <m> ) . . . . . . . for rational-based rcwa mapping
##
##  The vertices are labelled by 1..<m> instead of 0..<m>-1 (0 is identified
##  with 1, etc.) because in {\GAP}, permutations cannot move 0.
##
##  The result is returned as a GRAPE graph.
##
InstallMethod( TransitionGraph,
               "for rational-based rcwa mappings (RCWA)",
               true, [ IsRationalBasedRcwaMapping, IsPosInt ], 0,

  function ( f, m )

    local  M;

    M := TransitionMatrix(f,m); 
    return Graph(Group(()), [1..m], OnPoints,
                 function(i,j) return M[i][j] <> 0; end, true);
  end );

#############################################################################
##
#M  OrbitsModulo( <f>, <m> ) . . . . . . . .  for rational-based rcwa mapping
##
InstallMethod( OrbitsModulo,
               "for rational-based rcwa mappings (RCWA)", true,
               [ IsRationalBasedRcwaMapping, IsPosInt ], 0,

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
               "for rational-based rcwa mappings (RCWA)", true,
               [ IsRationalBasedRcwaMapping, IsPosInt ], 0,

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

#############################################################################
##
#F  Trajectory( <f>, <n>, <end>, <cond> )
##
InstallGlobalFunction( Trajectory,

  function ( f, n, val, cond )

    local  seq, step;

    if not (    IsRcwaMapping(f) and n in Source(f)
            and (     cond = "stop"
                  and (val in Source(f) or IsSubset(Source(f),val))
                  or  cond = "length" and IsPosInt(val)))
    then Error("for usage of `Trajectory' see manual.\n"); fi;
    seq := [n];
    if cond = "length" then
      for step in [1..val-1] do Add(seq,seq[step]^f); od;
    elif cond = "stop" then
      if not IsListOrCollection(val) then val := [val]; fi;
      repeat Add(seq,seq[Length(seq)]^f); until seq[Length(seq)] in val;
    fi;
    return seq;
  end );

#############################################################################
##
#F  TrajectoryModulo( <f>, <n>, <m>, <lng> ) . .  trajectory (mod <m>) of <f>
#F  TrajectoryModulo( <f>, <n>, <lng> )
##
InstallGlobalFunction( TrajectoryModulo,

  function ( arg )

    local  usage, f, n, m, lng, seq, i;

    usage := Concatenation("usage: TrajectoryModulo( <f>, <n>, [ <m> ], ",
                           "<lng> ), where <f> is an rcwa mapping, <n> and ",
                           "<m> are elements of its source and <lng> is a ",
                           "positive integer.\n");
    if not Length(arg) in [3,4] then Error(usage); fi;
    f := arg[1]; n := arg[2];
    if   Length(arg) = 3 then m := Modulus(f); lng := arg[3];
                         else m := arg[3];     lng := arg[4]; fi;
    if not (IsRcwaMapping(f) and IsSubset(Source(f),[m,n]) and IsPosInt(lng))
    then Error(usage); fi;
    seq := [];
    for i in [1..lng] do
      Add(seq,n mod m); n := n^f;
    od;
    return seq;
  end );

#############################################################################
##
#F  CoefficientsOnTrajectory( <f>, <n>, <end>, <cond>, <all> )
##
InstallGlobalFunction( CoefficientsOnTrajectory,

  function ( f, n, val, cond, all )

    local coeff, cycle, c, m, d, pos, res, r, deg, R, q, x;

    if not (    IsRcwaMapping(f) and n in Source(f)
            and (   val in Source(f) and cond = "stop"
                 or IsPosInt(val) and cond = "length")
            and all in [false,true])
    then Error("for usage of `CoefficientsOnTrajectory' see manual.\n"); fi;
    c := Coefficients(f); m := Modulus(f);
    cycle := [n];
    if   cond = "length"
    then for pos in [2..val] do Add(cycle,cycle[pos-1]^f); od;
    else repeat
           Add(cycle,cycle[Length(cycle)]^f);
         until cycle[Length(cycle)] = val;
    fi;
    if IsModularRcwaMapping(f) then
      deg := DegreeOfLaurentPolynomial(m);
      R   := Source(f);
      q   := Size(CoefficientsRing(R));
      x   := IndeterminatesOfPolynomialRing(R)[1];
      res := AllGFqPolynomialsModDegree(q,deg,x);
    else res := [0..m-1]; fi;
    coeff := [[1,0,1]*One(Source(f))];
    for pos in [1..Length(cycle)-1] do
      r := Position(res,cycle[pos] mod m);
      coeff[pos+1] := [ c[r][1] * coeff[pos][1],
                        c[r][1] * coeff[pos][2] + c[r][2] * coeff[pos][3],
                        c[r][3] * coeff[pos][3] ];
      d := Gcd(coeff[pos+1]);
      coeff[pos+1] := coeff[pos+1]/d;
    od;
    if all then return coeff; else return coeff[Length(coeff)]; fi;
  end );

#############################################################################
##
#M  PrimeSet( <f> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mapping
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
#M  IsTame( <f> ) . . . . . . . . . . . . . . . .  for bijective rcwa mapping
##
##  The `factors of multiplier and divisor' criterion.
##  This is only applicable for bijective mappings, e.g. n -> 2n
##  certainly isn't wild.
##
InstallMethod( IsTame,
               "for bijective rcwa mappings (RCWA)", true, [ IsRcwaMapping ],
               100,

  function ( f )

    local  R, mult, div;

    if   IsIntegral(f)
    then Info(InfoRCWA,4,"IsTame: mapping is integral, hence tame.");
         return true; fi;
    if not IsBijective(f) then TryNextMethod(); fi;
    Info(InfoRCWA,1,"IsTame:`factors of multiplier and divisor' criterion.");
    R := Source(f); mult := Multiplier(f); div := Divisor(f);
    if   Set(Factors(R,mult)) <> Set(Factors(R,div))
    then SetOrder(f,infinity); return false; else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  IsTame( <f> ) . . . . . . . . . . . . . . . .  for bijective rcwa mapping
##
##  The `dead end' criterion.
##  This is only applicable for bijective mappings.
##
InstallMethod( IsTame,
               "for bijective rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 50,

  function ( f )

    local  gamma, delta, C, r;

    if   not IsRationalBasedRcwaMapping(f) or not IsBijective(f)
    then TryNextMethod(); fi; # TransitionGraph f. mod. map's curr. not impl.
    Info(InfoRCWA,2,"IsTame:`dead end' criterion.");
    gamma := TransitionGraph(f,Modulus(f));
    for r in [1..Modulus(f)] do RemoveSet(gamma.adjacencies[r],r); od;
    delta := UnderlyingGraph(gamma);
    C := ConnectedComponents(delta);
    if   Position(List(C,V->Diameter(InducedSubgraph(gamma,V))),-1) <> fail
    then SetOrder(f,infinity); return false; else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  IsTame( <f> ) . . . . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
##  The `finite order or flat power' criterion.
##
InstallMethod( IsTame,
               "for rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 30,

  function ( f )

    local  pow, exp, e;

    Info(InfoRCWA,2,"IsTame:`finite order or integral power' criterion.");
    if IsBijective(f) and Order(f) <> infinity then return true; fi;
    pow := f; exp := [2,2,3,5,2,7,3,2,11,13,5,3,17,19,2]; e := 1;
    for e in exp do
      pow := pow^e;
      if IsIntegral(pow) then return true; fi;
      if   IsRationalBasedRcwaMapping(f) and Modulus(pow) > 6 * Modulus(f)
        or     IsModularRcwaMapping(f)
           and   DegreeOfLaurentPolynomial(Modulus(pow))
               > DegreeOfLaurentPolynomial(Modulus(f)) + 2
      then TryNextMethod(); fi;
    od;
    TryNextMethod();
  end );

#############################################################################
##
#M  IsTame( <f> ) . . . . . . . . . . . . . . for rational-based rcwa mapping
##
##  This is a probabilistic method.
##
InstallMethod( IsTame,
               "for rational-based rcwa mappings (RCWA)",
               true, [ IsRationalBasedRcwaMapping ], 0,
               
  function ( f )

    local  pow, maxmod, exp, maxexp, m;

    if IsBijective(f) and Order(f) < infinity then return true; fi;
    Info(InfoRCWA,1,"IsTame: probabilistic method.");
    maxmod := Modulus(f)^2; maxexp := maxmod; exp := 1; pow := f;
    repeat
      pow := pow * pow; m := Modulus(pow); exp := exp * 2;
    until exp > maxexp or m > maxmod;
    if m > maxmod then
      Info(InfoRCWA,3,"IsTame: the ",Ordinal(exp)," power of ",f," has ",
                      "Modulus ",m,"; this is larger than the square of the",
                      " modulus of the base, so we claim the mapping is ",
                      "wild, although the validity of this criterium has ",
                      "not yet been proved.");
    fi;
    return m <= maxmod;
  end );

# Single fixed points; <m> is the modulus of the group generated by <f>.

FixedPointsOfRcwaMapping := function ( f, m )
 
  local  fixedpoints, c, r, fp;

  c := Concatenation(List([1 .. m/f!.modulus], i -> f!.coeffs));
  fixedpoints := [];
  for r in [1..m] do
    if   c[r][1] <> c[r][3]
    then fp := -c[r][2] / (c[r][1] - c[r][3]);
         if   fp in Source(f) and fp mod m = r - 1 
         then Add(fixedpoints,fp); fi;
    fi;
  od;
  return fixedpoints;
end;
MakeReadOnlyGlobal( "FixedPointsOfRcwaMapping" );

# Whole fixed classes (mod <m>);
# <m> is the modulus of the group generated by <f>.

FixedClassesOfRcwaMapping := function ( f, m )
  return Filtered([0..m - 1], r -> f!.coeffs[r mod f!.modulus + 1]
                                 = [1,0,1]);
end;
MakeReadOnlyGlobal( "FixedClassesOfRcwaMapping" );

#############################################################################
##
#M  CycleOp( <sigma>, <n> ) . .  for rat.-based rcwa mapping and ring element
##
InstallOtherMethod( CycleOp,
                    Concatenation("for rational-based rcwa mapping ",
                                  "and ring element (RCWA)"),
                    true, [ IsRationalBasedRcwaMapping, IsRingElement ], 0,

  function ( sigma, n )

    local  cyc, n_i, lng, m, img;

    if not (n in Source(sigma) and IsBijective(sigma)) then return fail; fi;
    cyc := [n]; n_i := n; lng := 1; m := Modulus(Group(sigma));
    repeat
      img := n^sigma;
      if img <> n then Add(cyc,img); n_i := img; lng := lng + 1; fi; 
    until img = n or lng > m;
    if   lng > m
    then Info(InfoRCWA,1,"CycleOp: cycle is infinite."); return fail;
    fi;
    return cyc;
  end );

#############################################################################
##
#M  ShortCycles( <f>, <maxlng> ) . .  for rat.-based rcwa mapping and integer
##
InstallMethod( ShortCycles,
               "for rational-based rcwa mappings (RCWA)",
               true, [ IsRationalBasedRcwaMapping, IsPosInt ], 0,

  function ( f, maxlng )

    local  cycles, cyclesbuf, cycs, cyc, pow, exp, min, minshift, l, i;

    cycles := []; pow := IdentityIntegralRcwaMapping;
    for exp in [1..maxlng] do
      pow := pow * f;
      cycs := List(FixedPointsOfRcwaMapping(pow,Modulus(pow)), n -> [n]);
      for cyc in cycs do
        for i in [1..exp-1] do Add(cyc,cyc[i]^f); od;
      od;
      cycles := Concatenation(cycles,cycs);
    od;
    cycles := Filtered(cycles, cyc -> Length(Set(cyc)) = Length(cyc));
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
#M  CycleType( <f> ) . . . . . . . . . . . . . for tame integral rcwa mapping
##
InstallMethod( CycleType,
               "for tame integral rcwa mappings (RCWA)",
               true, [ IsIntegralRcwaMapping ], 0,
               
  function ( f )

    if not IsTame(f) then TryNextMethod(); fi;
    StandardConjugate(f);
    return CycleType(f);
  end );

#############################################################################
##
#M  RespectedClassPartition( <sigma> ) . . .  for tame bijective rcwa mapping
##
InstallMethod( RespectedClassPartition,
               "for tame bijective rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 0,

  function ( sigma )
    if not IsBijective(sigma) then return fail; fi;
    return RespectedClassPartition( Group( sigma ) );
  end );

ReducedSetOfStartingValues := function ( S, f, lng )

  local  n, min, max, traj;

  min := Minimum(S); max := Maximum(S);
  for n in [min..max] do
    if n in S then
      traj := Set(Trajectory(f,n,lng,"length"){[2..lng]});
      if not n in traj then S := Difference(S,traj); fi;
    fi;
  od;
  return S;
end;
MakeReadOnlyGlobal( "ReducedSetOfStartingValues" );

#############################################################################
##
#M  ContractionCentre( <f>, <maxn>, <bound> ) . . . for integral rcwa mapping
##
InstallMethod( ContractionCentre,
               "for integral rcwa mappings (RCWA)", true,
               [ IsIntegralRcwaMapping, IsPosInt, IsPosInt ], 0,

  function ( f, maxn, bound )

    local  S0, S, n, n_i, i, seq;

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
          S0 := Union(S0,Trajectory(f,n_i,n_i,"stop"));
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
#M  RestrictedPerm( <g>, <S> ) . . . . . . . . . . . . . .  for rcwa mappings
##
InstallOtherMethod( RestrictedPerm,
                    "for rcwa mappings (RCWA)", true,
                    [ IsRcwaMapping, IsUnionOfResidueClasses ], 0,

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
#M  Restriction( <g>, <f> ) . . . . . . . . . . .  for integral rcwa mappings
##
InstallMethod( Restriction,
               "for integral rcwa mappings (RCWA)", true,
               [ IsIntegralRcwaMapping, IsIntegralRcwaMapping ], 0,

  function ( g, f )

    local  mgf, gf, c, fixed, r;

    if not IsInjective(f) then return fail; fi;
    mgf := Multiplier(f) * Modulus(f)^2 * Modulus(g); c := [];
    for r in [0..2*mgf-1] do
      Append(c,[[r^f,(r^g)^f],[(r+mgf)^f,((r+mgf)^g)^f]]);
    od;
    fixed := Difference([0..mgf-1],Set(List(c,t->t[1] mod mgf)));
    for r in fixed do c := Concatenation(c,[[r,r],[r+mgf,r+mgf]]); od; 
    gf := RcwaMapping(mgf,c);
    if   g*f <> f*gf
    then Error("Restriction: Diagram does not commute.\n"); fi;

    if HasIsInjective(g)  then SetIsInjective(gf,IsInjective(g)); fi;
    if HasIsSurjective(g) then SetIsSurjective(gf,IsSurjective(g)); fi;
    if HasIsTame(g)       then SetIsTame(gf,IsTame(g)); fi;
    if HasOrder(g)        then SetOrder(gf,Order(g)); fi;

    return gf;
  end );

#############################################################################
##
#M  Divergence( <f> ) . . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
InstallMethod( Divergence,
               "for rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,

  function ( f )

    local  R, pow, m, c, M, approx, prev, facts, p, NrRes, exp, eps, prec;

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
#M  ImageDensity( <f> ) . . . . . . . . . . . . . . . . . .  for rcwa mapping
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
#M  CompatibleConjugate( <g>, <h> ) . . . . . . .  for integral rcwa mappings
##
InstallMethod( CompatibleConjugate,
               "for integral rcwa mappings (RCWA)", true,
               [ IsIntegralRcwaMapping, IsIntegralRcwaMapping ], 0,

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
    Pg := RespectedClassPartition(g); Ph := RespectedClassPartition(h);
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
#E  rcwamap.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here

