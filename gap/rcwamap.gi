#############################################################################
##
#W  rcwamap.gi                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains implementations of methods and functions for
##  computing with rcwa mappings.
##
##  We define *residue class-wise affine* mappings (*rcwa mappings*) of a
##  PID $R$ without zero-divisors such that for any non-zero ideal $I$ of $R$
##  the quotient $R/I$ is finite, as mappings $f : R \rightarrow R$ whose
##  restrictions to the residue classes modulo some ideal $I = <m>$ are
##  restrictions of affine mappings of the quotient field of $R$ to the
##  respective class. We call $m$ the modulus of $f$. 
##
##  The (pointwise) sum and the product (composition) of two such mappings
##  is an rcwa mapping again (in general certainly not with the same modulus
##  as the operands).
##  The bijective rcwa mappings form a multiplicative group that we call
##  the *rcwa group* of the ring $R$. We write RCWA($R$).
##  It obviously holds that RCWA($R$) \< Sym($R$), hence the set of elements
##  of RCWA($R$) can be considered as a class of, usually infinite,
##  permutations.
##  We call a group homomorphism $\phi : G \rightarrow$ RCWA($R$), where $G$
##  is an arbitrary (possibly infinite) group, an $R$-*rcwa-representation*
##  of $G$.
##
##  Caution: The zero mapping multiplicatively is only a right zero element 
##           ($a*0 = 0$ for all $a$, but $0*a = 0$ if and only if
##           $0^a = 0$), and it holds only the left distributive law
##           ($a*(b+c) = a*b+a*c$, but not necessary $(a+b)*c = a*c+b*c$).
##
##  Some remarks concerning the implementation of rcwa mappings of
##  the ring of integers:
##
##  An integral rcwa mapping object <f> just stores the modulus <modulus>
##  and a coefficients list <coeffs>.
##  The list <coeffs> consists of <modulus> lists of length 3, where
##  <coeffs>[<a> + 1]> gives the coefficients of the mapping on the residue
##  class <a> mod <modulus>, hence if <n> mod <modulus> = <a>, we have 
##  $$
##    <n>^<f> = (<coeffs>[<a> + 1][1] * <n> + <coeffs>[<a> + 1][2]) /
##               <coeffs>[<a> + 1][3]>.
##  $$
##  A semilocal integral rcwa mapping object (here, the underlying ring
##  is $\Z_{\pi}$ for a set of primes $\pi$) stores the same information,
##  the set of of non-invertible primes in the base ring is stored in its
##  family object.
##
##  Some remarks concerning the implementation of rcwa mappings of
##  GF(<q>)[<x>] (modular rcwa mappings):
## 
##  A modular rcwa mapping object stores the finite field size <q>, the
##  modulus <modulus> and a coefficients list <coeffs>.
##  The meaning of <modulus> and <coeffs> is completely analogous to the
##  above, where the residue classes for <coeffs> are sorted according to
##  the default order of their smallest-degree representatives in {\GAP}.
##
##  The following applies to all kinds of rcwa mappings:
##
##  To prevent unnecessary coefficient explosion, the mapping <f> is always
##  represented with the smallest possible modulus, and the 3 coefficients
##  of <f> on a specific residue class are ensured to be coprime.
##
Revision.rcwamap_gi :=
  "@(#)$Id$";

#############################################################################
##
#F  RCWAInfo . . . . . . . . . . . . . . . . . . set info level of `RcwaInfo'
##
InstallGlobalFunction( RCWAInfo,
                       function ( n ) SetInfoLevel( RcwaInfo, n ); end );

#############################################################################
##
#V  IntegralRcwaMappingsFamily . . . the family of all integral rcwa mappings
##
InstallValue( IntegralRcwaMappingsFamily,
              NewFamily( "IntegralRcwaMappingsFamily",
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
#F  SemilocalIntegralRcwaMappingsFamily( <primes> )
##
##  Family of <primes>-semilocal integral rcwa mappings.
##
InstallGlobalFunction( SemilocalIntegralRcwaMappingsFamily,

  function ( primes )

    local  fam, name;

    if   not IsSet(primes) or not ForAll(primes,IsPrimeInt)
    then Error("usage: SemilocalIntegralRcwaMappingsFamily( <primes> )\n",
               "for a set of primes <primes>.\n");
    fi;
    name := Concatenation( "SemilocalIntegralRcwaMappingsFamily( ",
                           String(primes)," )" );
    fam := NewFamily( name, IsSemilocalIntegralRcwaMapping,
                      CanEasilySortElements, CanEasilySortElements );
    SetUnderlyingRing( fam, Z_pi( primes ) );
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

  function ( q )

    local  fam, R, x, IndName;

    if   not IsPrimePowerInt( q )
    then Error("usage: ModularRcwaMappingsFamily( <q> ) for a ",
               "prime power <q>.\n");
    fi;
    R := PolynomialRing( GF( q ), [ 1 ] );
    x := IndeterminatesOfPolynomialRing( R )[ 1 ];
    if   not HasIndeterminateName( FamilyObj( x ), 1 )
    then SetIndeterminateName( FamilyObj( x ), 1, "x" ); fi; 
    IndName := IndeterminateName( FamilyObj( x ), 1 ); 
    fam := NewFamily( Concatenation( "ModularRcwaMappingsFamily( GF( ",
                                     String(q), " )[ ", IndName, " ] )" ),
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

InstallTrueMethod( IsMapping,     IsRcwaMapping );
InstallTrueMethod( IsRcwaMapping, IsRationalBasedRcwaMapping );
InstallTrueMethod( IsRationalBasedRcwaMapping, IsIntegralRcwaMapping );
InstallTrueMethod( IsRationalBasedRcwaMapping,
                   IsSemilocalIntegralRcwaMapping );
InstallTrueMethod( IsRcwaMapping, IsModularRcwaMapping );

#############################################################################
##
#F  AllGFqPolynomialsModDegree( <q>, <d>, <x> ) . residues in canonical order
##
InstallGlobalFunction ( AllGFqPolynomialsModDegree,

  function ( q, d, x )
    if   d <> 0
    then return List( Tuples( GF( q ), d ),
                      t -> Sum( List( [ 1 .. d ], i -> t[i] * x^(d-i) ) ) );
    else return [ 0 * One( x ) ]; fi;
  end );

# Bring the rcwa mapping <f> to normalized, reduced form.

ReduceIntegralRcwaMapping := function ( f )

  local  c, m, divs, d, cRed, n, i;

  c := f!.coeffs; m := f!.modulus;
  for n in [1..Length(c)] do
    d := Gcd(c[n]);
    c[n] := c[n]/d;
    if c[n][3] < 0 then c[n] := -c[n]; fi;
  od;
  divs := DivisorsInt(m); i := 1;
  repeat
    d := divs[i]; i := i + 1;
    cRed := List([1..m/d], i -> c{[(i - 1) * d + 1 .. i * d]});
  until Length(Set(cRed)) = 1;
  f!.coeffs  := Immutable(cRed[1]);
  f!.modulus := Length(cRed[1]);
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

#############################################################################
##
#F  IntegralRcwaMappingNC( <coeffs> )
#F  IntegralRcwaMappingNC( <perm>, <range> )
#F  IntegralRcwaMappingNC( <modulus>, <val> )
##
InstallGlobalFunction( IntegralRcwaMappingNC,

  function ( arg )

    local coeffs, perm, range, val, min, max, m, n, r, pts, Result;

    if   Length(arg) = 1 
    then coeffs := arg[1];
    elif IsPerm(arg[1]) and IsRange(arg[2])
    then perm := arg[1]; range := arg[2];
         min := Minimum(range); max := Maximum(range);
         m := max - min + 1; coeffs := [];
         for n in [min..max] do
           r := n mod m + 1;
           coeffs[r] := [1, n^perm - n, 1];
         od;
    else m := arg[1]; val := Set(arg[2]); coeffs := [];
         for r in [1..m] do
           pts := Filtered(val, pt -> pt[1] mod m = r - 1);
           coeffs[r] := [  pts[1][2] - pts[2][2],
                           pts[1][2] * (pts[1][1] - pts[2][1])
                         - pts[1][1] * (pts[1][2] - pts[2][2]),
                           pts[1][1] - pts[2][1]];
         od;
    fi;
    Result := Objectify( NewType(    IntegralRcwaMappingsFamily,
                                     IsIntegralRcwaMapping
                                 and IsRationalBasedRcwaDenseRep ),
                         rec( coeffs  := coeffs,
                              modulus := Length(coeffs) ) );
    SetSource(Result, Integers);
    SetRange (Result, Integers);
    ReduceIntegralRcwaMapping(Result);

    return Result;
  end );

#############################################################################
##
#F  IntegralRcwaMapping( <coeffs> )
#F  IntegralRcwaMapping( <perm>, <range> )
#F  IntegralRcwaMapping( <modulus>, <val> )
##
InstallGlobalFunction( IntegralRcwaMapping,

  function ( arg )

    local coeffs, perm, range, val, min, max, m, n, r, pts, Result,
          quiet;

    quiet := ValueOption("BeQuiet") = true;
    if   Length(arg) = 1 
    then coeffs := arg[1];
         if not (IsList(coeffs) and ForAll(Flat(coeffs),IsInt)
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
    elif IsPerm(arg[1]) and IsRange(arg[2])
    then perm := arg[1]; range := arg[2];
         if   Permutation(perm,range) = fail
         then if quiet then return fail; fi;
              Error("the permutation ",perm," does not act on the range ",
                    range,".\n");
         fi;
    elif IsPosInt(arg[1]) and IsList(arg[2])
         and Set(List(arg[2],Length)) = [2] and ForAll(Flat(arg[2]),IsInt)
    then
      m := arg[1]; val := Set(arg[2]); coeffs := [];
      for r in [1..m] do
        pts := Filtered(val, pt -> pt[1] mod m = r - 1);
        if   Length(pts) < 2 
        then if quiet then return fail; fi;
             Error("the mapping is not given at at least 2 points <n> ",
                   "with <n> mod ",m," = ",r - 1,".\n");
        fi;
      od;
    else if quiet then return fail; fi;
         Error("see RCWA Manual for usage of IntegralRcwaMapping.\n");
    fi;

    Result := CallFuncList( IntegralRcwaMappingNC, arg );

    if   IsBound(val)
    then if not ForAll(val, t -> t[1]^Result = t[2])
         then if quiet then return fail; fi;
              Error("the values ",val," do not define a proper integral ",
                    "rcwa mapping.\n"); 
         fi;
    fi;

    return Result;
  end );

#############################################################################
##
#F  SemilocalIntegralRcwaMappingNC( <pi>, <coeffs> )
##
InstallGlobalFunction( SemilocalIntegralRcwaMappingNC,

  function ( pi, coeffs )

    local fam, Result;

    if IsInt(pi) then pi := [pi]; fi;
    fam := First( Z_PI_RCWAMAPPING_FAMILIES,
                  f -> NoninvertiblePrimes(UnderlyingRing(f)) = pi );
    if fam = fail then fam := SemilocalIntegralRcwaMappingsFamily(pi); fi;
    Result := Objectify( NewType(    fam,
                                     IsSemilocalIntegralRcwaMapping
                                 and IsRationalBasedRcwaDenseRep ),
                         rec( coeffs  := coeffs,
                              modulus := Length(coeffs) ) );
    SetSource(Result, UnderlyingRing( fam ) );
    SetRange (Result, UnderlyingRing( fam ) );
    ReduceSemilocalIntegralRcwaMapping(Result);

    return Result;
  end );

#############################################################################
##
#F  SemilocalIntegralRcwaMapping( <pi>, <coeffs> )
##
InstallGlobalFunction( SemilocalIntegralRcwaMapping,

  function ( pi, coeffs )

    local  R, n, r, pts, Result, quiet;

    quiet := ValueOption("BeQuiet") = true;
    R := Z_pi(pi);
    if not (    IsList(coeffs)
            and IsSubset(Union(pi,[1]),Set(Factors(Length(coeffs))))
            and ForAll(Flat(coeffs),
                       x -> IsRat(x) and Intersection(pi,
                                         Set(Factors(DenominatorRat(x))))=[])
            and ForAll(coeffs, IsList)
            and ForAll(coeffs, c -> Length(c) = 3)
            and ForAll([0..Length(coeffs) - 1],
                       n -> coeffs[n + 1][3] <> 0 and
                            NumeratorRat(n * coeffs[n + 1][1]
                                           + coeffs[n + 1][2])
                            mod StandardAssociate(R,coeffs[n + 1][3]) = 0 and
                            NumeratorRat(  (n + Length(coeffs))
                                          * coeffs[n + 1][1]
                                          + coeffs[n + 1][2])
                            mod StandardAssociate(R,coeffs[n + 1][3]) = 0))
    then if quiet then return fail; fi;
         Error("the coefficients ",coeffs," do not define a proper ",
               pi," - semilocal integral rcwa mapping.\n");
    fi;

    Result := SemilocalIntegralRcwaMappingNC( pi, coeffs );

    return Result;
  end );

#############################################################################
##
#F  ModularRcwaMappingNC( <q>, <modulus>, <coeffs> )
##
InstallGlobalFunction( ModularRcwaMappingNC,

  function ( q, modulus, coeffs )

    local  Result, R, fam;

    fam := First( MODULAR_RCWAMAPPING_FAMILIES,
                  f -> Size(CoefficientsRing(UnderlyingRing(f))) = q );
    if fam = fail then fam := ModularRcwaMappingsFamily(q); fi;
    Result := Objectify( NewType( fam, IsModularRcwaMapping
                                   and IsModularRcwaDenseRep ),
                         rec( coeffs  := coeffs,
                              modulus := modulus ) );
    R := UnderlyingRing( fam );
    SetUnderlyingField( Result, CoefficientsRing( R ) );
    SetSource( Result, R ); SetRange( Result, R );
    ReduceModularRcwaMapping(Result);

    return Result;
  end );

#############################################################################
##
#F  ModularRcwaMapping( <q>, <modulus>, <coeffs> )
##
InstallGlobalFunction( ModularRcwaMapping,

  function ( q, modulus, coeffs )

    local  d, x, R, P, quiet;

    quiet := ValueOption("BeQuiet") = true;
    if not (    IsPosInt(q) and IsPrimePowerInt(q) 
            and IsPolynomial(modulus) and IsList(coeffs)
            and ForAll(coeffs, c -> Length(c) = 3) 
            and ForAll(Flat(coeffs), IsPolynomial))
    then if quiet then return fail; fi;
         Error("usage: ModularRcwaMapping( <q>, <modulus>, <coeffs> )\n",
               "where <q> is the size of the coefficients field, ",
               "<modulus> is an element of\nits underlying ring and ",
               "<coeffs> is a suitable coefficients list.\n");
    fi;
    d := DegreeOfLaurentPolynomial(modulus);
    x := IndeterminateOfLaurentPolynomial(coeffs[1][1]);
    R := PolynomialRing(GF(q),
           IndeterminateNumberOfLaurentPolynomial(coeffs[1][1]));
    P := AllGFqPolynomialsModDegree(q,d,x);
    if not ForAll([1..Length(P)],
                  i -> IsZero(   (coeffs[i][1]*P[i] + coeffs[i][2])
                              mod coeffs[i][3]))
    then Error("the coefficients ",coeffs," do not define a proper ",
               "modular rcwa mapping.\n");
    fi;

    return ModularRcwaMappingNC( q, modulus, coeffs );
  end );

#############################################################################
##
#F  RcwaMapping( <coeffs> )
#F  RcwaMapping( <perm>, <range> )
#F  RcwaMapping( <modulus>, <val> )
#F  RcwaMapping( <pi>, <coeffs> )
#F  RcwaMapping( <q>, <modulus>, <coeffs> )
##
InstallGlobalFunction( RcwaMapping,

  function ( arg )

    if    Length( arg ) = 2 and ( IsInt( arg[1] ) or IsList( arg[1] ) )
      and IsList( arg[2] ) and Set( List( arg[2], Length ) ) = [ 3 ]
    then return CallFuncList( SemilocalIntegralRcwaMapping, arg );
    elif Length( arg ) = 3
    then return CallFuncList( ModularRcwaMapping, arg );
    else return CallFuncList( IntegralRcwaMapping, arg );
    fi;
  end );

IdChars := function ( n, ch )
  return Concatenation( ListWithIdenticalEntries( n, ch ) );
end;
MakeReadOnlyGlobal( "IdChars" );

#############################################################################
##
#M  String( <f> ) . . . . . for univariate polynomial ring over finite field
##
InstallMethod( String,
               "for univariate polynomial rings over finite fields",
               true, [ IsUnivariatePolynomialRing ], 0,

  function ( R )

    local  F, q, x, IndNr, IndName;

    F := CoefficientsRing(R); q := Size(F);
    if not IsFinite(F) or F <> GF(q) then TryNextMethod(); fi;
    x := IndeterminatesOfPolynomialRing(R)[1];
    IndNr := IndeterminateNumberOfUnivariateLaurentPolynomial(x);
    IndName := IndeterminateName(FamilyObj(x),IndNr);
    if   IndName = fail
    then IndName := Concatenation("x_",String(IndNr)); fi;
    return Concatenation( "GF(", String(q), ")[", IndName, "]" );
  end );

#############################################################################
##
#M  ViewObj( <f> ) . . . . . for univariate polynomial ring over finite field
##
InstallMethod( ViewObj,
               "for univariate polynomial rings over finite fields",
               true, [ IsUnivariatePolynomialRing ], 100,

  function ( R )

    local  F, q;

    F := CoefficientsRing(R); q := Size(F);
    if not IsFinite(F) or F <> GF(q) then TryNextMethod(); fi;
    Print(String(R));
  end );

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
       Print(")/",c);
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

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( PrintObj,
               "for integral rcwa mappings", true,
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep ], 0,

  function ( f )
    Print( "IntegralRcwaMapping( ", f!.coeffs, " )" );
  end );

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . for semilocal integral rcwa mapping
##
InstallMethod( PrintObj,
               "for semilocal integral rcwa mappings",
               true, [     IsSemilocalIntegralRcwaMapping 
                       and IsRationalBasedRcwaDenseRep ], 0,

  function ( f )
    Print( "SemilocalIntegralRcwaMapping( ",
           NoninvertiblePrimes(Source(f)), ", ", f!.coeffs, " )" );
  end );

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . . . . . .  for modular rcwa mapping
##
InstallMethod( PrintObj,
               "for modular rcwa mappings",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,

  function ( f )
    Print( "ModularRcwaMapping( ", Size(UnderlyingField(f)),
           ", ", f!.modulus, ", ", f!.coeffs, " )" );
  end );

#############################################################################
##
#M  String( <f> ) . . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( String,
               "for integral rcwa mappings", true,
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep ], 0,

  function ( arg )

    local f, lng, s;

    f := arg[1]; if Length(arg) > 1 then lng := arg[2]; fi;
    s := Concatenation( "IntegralRcwaMapping( ", String( f!.coeffs ), " )" );
    if IsBound(lng) then s := String(s,lng); fi;
    return s;
  end );

#############################################################################
##
#M  String( <f> ) . . . . . . . . . . . . for semilocal integral rcwa mapping
##
InstallMethod( String,
               "for semilocal integral rcwa mappings",
               true, [     IsSemilocalIntegralRcwaMapping
                       and IsRationalBasedRcwaDenseRep ], 0,

  function ( arg )

    local  f, lng, s;

    f := arg[1]; if Length(arg) > 1 then lng := arg[2]; fi;
    s := Concatenation( "SemilocalIntegralRcwaMapping( ",
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
               "for modular rcwa mappings",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,

  function ( arg )

    local  f, lng, s;

    f := arg[1]; if Length(arg) > 1 then lng := arg[2]; fi;
    s := Concatenation( "ModularRcwaMapping( ",
                        String(Size(UnderlyingField(f))), ", ",
                        String(f!.modulus), ", ", String(f!.coeffs), " )" );
    if IsBound(lng) then s := String(s,lng); fi;
    return s;
  end );

#############################################################################
##
#M  ViewObj( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
InstallMethod( ViewObj,
               "for rational-based and modular rcwa mappings",
               true, [ IsRcwaMapping ], 0,

  function ( f )

    if IsZero(f) or IsOne(f) then View(f); return; fi;
    if IsOne(Modulus(f)) then Display(f:NoLineFeed); return; fi;
    if not (IsRationalBasedRcwaDenseRep(f) or IsModularRcwaDenseRep(f))
    then TryNextMethod(); fi;
    Print("<");
    if   HasIsBijective(f) and IsBijective(f) 
    then Print("bijective ");
    elif HasIsInjective(f) and IsInjective(f)
    then Print("injective ");
    elif HasIsSurjective(f) and IsSurjective(f)
    then Print("surjective ");
    fi;
    if   IsIntegralRcwaMapping(f)
    then Print("integral rcwa mapping");
    else Print("rcwa mapping of ",String(Source(f))); fi;
    Print(" with modulus ",f!.modulus);
    if HasOrder(f) then Print(", of order ",Order(f)); fi;
    Print(">");
  end );

#############################################################################
##
#M  Display( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
##  Display the rcwa mapping <f> as a nice, human-readable table.
##
InstallMethod( Display,
               "for rational-based and modular rcwa mappings",
               true, [ IsRcwaMapping ], 0,

  function ( f )

    local  m, c, pi, q, d, x, RingString, name, VarName,
           r, NrResidues, poses, pos, t, i, scr, l1, l2, l3, str,
           mdec, mstr, MaxPolLng, FlushLng, prefix;

    if not (IsRationalBasedRcwaDenseRep(f) or IsModularRcwaDenseRep(f))
    then TryNextMethod(); fi;
    m := f!.modulus; c := f!.coeffs;
    if HasName(f) then name := Name(f); else name := "f"; fi;
    prefix := false;
    if not IsIntegralRcwaMapping(f) then RingString := String(Source(f)); fi;
    if   IsModularRcwaMapping(f)
    then VarName := "P"; q := Size(UnderlyingField(f));
         d := DegreeOfLaurentPolynomial(m); NrResidues := q^d;
         x := IndeterminatesOfPolynomialRing(Source(f))[1];
         r := AllGFqPolynomialsModDegree(q,d,x);
         MaxPolLng := Maximum(List(r,p->Length(String(p))));
    else VarName := "n"; NrResidues := m; fi;
    if   IsOne(f)
    then if   IsIntegralRcwaMapping(f)
         then Print("Identity integral rcwa mapping");
         else Print("Identity rcwa mapping of ",RingString); fi;  
    elif IsZero(f)
    then if   IsIntegralRcwaMapping(f)
         then Print("Zero integral rcwa mapping");
         else Print("Zero rcwa mapping of ",RingString); fi;
    elif IsOne(m) and IsZero(c[1][1])
    then if   IsIntegralRcwaMapping(f)
         then Print("Constant integral rcwa mapping with value ",c[1][2]);
         else Print("Constant rcwa mapping of ",RingString,
                    " with value ",c[1][2]); fi;
    else if not IsOne(m) then Print("\n"); fi;
         if   HasIsBijective(f) and IsBijective(f)
         then Print("Bijective "); prefix := true;
         elif HasIsInjective(f) and IsInjective(f)
         then Print("Injective "); prefix := true;
         elif HasIsSurjective(f) and IsSurjective(f)
         then Print("Surjective "); prefix := true;
         fi;
         if IsIntegralRcwaMapping(f) then
           if prefix then Print("integral rcwa mapping");
                     else Print("Integral rcwa mapping"); fi;
         else
           if prefix then Print("rcwa"); else Print("Rcwa"); fi;
           Print(" mapping of ",RingString);
         fi;
         if IsOne(m) then
           Print(": ",VarName," -> ");
           if   IsIntegralRcwaMapping(f)
           then DisplayIntegralAffineMapping(c[1]);
           elif IsSemilocalIntegralRcwaMapping(f)
           then DisplaySemilocalIntegralAffineMapping(c[1]);
           else DisplayModularAffineMapping(c[1],SizeScreen()[1]-48); fi;
         else
           Print(" with modulus ",m);
           if HasOrder(f) then Print(", of order ",Order(f)); fi;
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
#M  \=( <f>, <g> ) . . . . . . . . . . . . for "rational-based" rcwa mappings
##
InstallMethod( \=,
               "for two rational-based rcwa mappings",
               IsIdenticalObj,
               [     IsRationalBasedRcwaMapping
                 and IsRationalBasedRcwaDenseRep,
                     IsRationalBasedRcwaMapping
                 and IsRationalBasedRcwaDenseRep ], 0,

  function ( f, g )
    return f!.coeffs = g!.coeffs;
  end );

#############################################################################
##
#M  \=( <f>, <g> ) . . . . . . . . . . . . . . . .  for modular rcwa mappings
##
InstallMethod( \=,
               "for two modular rcwa mappings",
               IsIdenticalObj,
               [ IsModularRcwaMapping and IsModularRcwaDenseRep,
                 IsModularRcwaMapping and IsModularRcwaDenseRep ],
               0,

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
               "for two rcwa mappings",
               IsIdenticalObj, [ IsRcwaMapping, IsRcwaMapping ], 0,

  function ( f, g )
    if   f!.modulus <> g!.modulus
    then return f!.modulus < g!.modulus;
    else return f!.coeffs  < g!.coeffs; fi;
  end );

#############################################################################
##
#V  ZeroIntegralRcwaMapping . . . . . . . . . . .  zero integral rcwa mapping
##
InstallValue( ZeroIntegralRcwaMapping,
              IntegralRcwaMapping( [ [ 0, 0, 1 ] ] ) );
SetIsZero( ZeroIntegralRcwaMapping, true );

#############################################################################
##
#V  IdentityIntegralRcwaMapping . . . . . . .  identity integral rcwa mapping
##
InstallValue( IdentityIntegralRcwaMapping,
              IntegralRcwaMapping( [ [ 1, 0, 1 ] ] ) );
SetIsOne( IdentityIntegralRcwaMapping, true );

#############################################################################
##
#M  ZeroOp( <f> ) . . . . . . . . . . . . . . . . . for integral rcwa mapping
##
##  Zero rcwa mapping.
##
InstallMethod( ZeroOp,
               "for integral rcwa mappings", true,
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep ], 0,
               f -> ZeroIntegralRcwaMapping );

#############################################################################
##
#M  ZeroOp( <f> ) . . . . . . . . . . . . for semilocal integral rcwa mapping
##
##  Zero rcwa mapping.
##
InstallMethod( ZeroOp,
               "for semilocal integral rcwa mappings",
               true, [     IsSemilocalIntegralRcwaMapping 
                       and IsRationalBasedRcwaDenseRep ], 0,
  function ( f )

    local  zero;

    zero := SemilocalIntegralRcwaMappingNC( NoninvertiblePrimes(Source(f)),
                                            [[0,0,1]] );
    SetIsZero( zero, true ); return zero;
  end );

#############################################################################
##
#M  ZeroOp( <f> ) . . . . . . . . . . . . . . . . .  for modular rcwa mapping
##
##  Zero rcwa mapping.
##
InstallMethod( ZeroOp,
               "for modular rcwa mappings",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,

  function ( f )

    local  zero;

    zero := ModularRcwaMappingNC( Size(UnderlyingField(f)), One(Source(f)),
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
               "for rcwa mappings", true, [ IsRcwaMapping ], 0,
               f -> f!.coeffs = [ [ 0, 0, 1 ] ] * One( Source( f ) ) );  

#############################################################################
##
#M  OneOp( <f> ) . . . . . . . . . . . . . . . . .  for integral rcwa mapping
##
##  Identity rcwa mapping.
##
InstallMethod( OneOp,
               "for integral rcwa mappings", true,
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep ], 0,
               f -> IdentityIntegralRcwaMapping );

#############################################################################
##
#M  OneOp( <f> ) . . . . . . . . . . . .  for semilocal integral rcwa mapping
##
##  Identity rcwa mapping.
##
InstallMethod( OneOp,
               "for semilocal integral rcwa mappings",
               true, [     IsSemilocalIntegralRcwaMapping 
                       and IsRationalBasedRcwaDenseRep ], 0,
  function ( f )

    local  one;
 
    one := SemilocalIntegralRcwaMappingNC( NoninvertiblePrimes(Source(f)),
                                           [[1,0,1]] );
    SetIsOne( one, true ); return one;
  end );


#############################################################################
##
#M  OneOp( <f> ) . . . . . . . . . . . . . . . . . . for modular rcwa mapping
##
##  Identity rcwa mapping.
##
InstallMethod( OneOp,
               "for modular rcwa mappings",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,

  function ( f )

    local  one;
 
    one := ModularRcwaMapping( Size(UnderlyingField(f)), One(Source(f)),
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
               "for rcwa mappings", true, [ IsRcwaMapping ], 0,
               f -> f!.coeffs = [ [ 1, 0, 1 ] ] * One( Source( f ) ) );  

#############################################################################
##
##  For the following operations `Coefficients', `Modulus', `Multiplier' and
##  `Divisor', it will be necessary to introduce separate methods for
##  integral, semilocal integral and modular rcwa mappings, as soon as there
##  will be other representations than IsRationalBasedRcwaDenseRep resp.
##  IsModularRcwaDenseRep.
##

#############################################################################
##
#M  Coefficients( <f> ) . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
InstallOtherMethod( Coefficients,
                    "for rcwa mappings",
                    true, [ IsRcwaMapping ], 0, f -> f!.coeffs );

#############################################################################
##
#M  Modulus( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
InstallMethod( Modulus,
               "for rcwa mappings",
               true, [ IsRcwaMapping ], 0, f -> f!.modulus );

#############################################################################
##
#M  Multiplier( <f> ) . . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
InstallMethod( Multiplier,
               "for rcwa mappings",
               true, [ IsRcwaMapping ], 0,
               f -> Lcm( List( f!.coeffs, c -> c[ 1 ] ) ) );

#############################################################################
##
#M  Multiplier( <f> ) . . . . . . . . . . for semilocal integral rcwa mapping
##
InstallMethod( Multiplier,
               "for semilocal integral rcwa mappings",
               true, [     IsSemilocalIntegralRcwaMapping
                       and IsRationalBasedRcwaDenseRep ], 10,

  f -> Lcm( List( f!.coeffs, c -> StandardAssociate( Source(f), c[1] ) ) ) );

#############################################################################
##
#M  Divisor( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
InstallMethod( Divisor,
               "for rcwa mappings",
               true, [ IsRcwaMapping ], 0,
               f -> Lcm( List( f!.coeffs, c -> c[ 3 ] ) ) );

#############################################################################
##
#M  IsFlat( <f> ) . . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( IsFlat,
               "for integral rcwa mappings",
               true, [     IsIntegralRcwaMapping
                       and IsRationalBasedRcwaDenseRep ], 0,

  f -> IsSubset( [-1,1], Set( Flat( List( f!.coeffs, c -> c{[1,3]} ) ) ) ) );

#############################################################################
##
#M  IsFlat( <f> ) . . . . . . . . . . . . for semilocal integral rcwa mapping
##
InstallMethod( IsFlat,
               "for semilocal integral rcwa mappings",
               true, [ IsSemilocalIntegralRcwaMapping ], 10,
               f -> [ Multiplier(f), Divisor(f) ] = [ 1, 1 ] );

#############################################################################
##
#M  IsFlat( <f> ) . . . . . . . . . . . . . . . . .  for modular rcwa mapping
##
InstallMethod( IsFlat,
               "for modular rcwa mappings",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,
               f ->  ForAll( Flat( List( f!.coeffs, c -> c{ [ 1, 3 ] } ) ),
                             p -> DegreeOfLaurentPolynomial( p ) = 0 ) );

#############################################################################
##
#M  IsClassWiseOrderPreserving( <f> ) . . . for "rational-based" rcwa mapping
##
InstallMethod( IsClassWiseOrderPreserving,
               "for rational-based rcwa mappings",
               true, [     IsRationalBasedRcwaMapping 
                       and IsRationalBasedRcwaDenseRep ], 0,
               f -> ForAll( f!.coeffs, c -> c[ 1 ] >= 0 ) );

#############################################################################
##
#M  ImageElm( <f>, <n> ) . . . . . . .  for integral rcwa mapping and integer
##
##  Image of the integer <n> under the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "for integral rcwa mapping and integer",
               true, [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep,
                       IsInt ], 0,

  function ( f, n )

    local Coeffs, Modulus;

    Modulus := f!.modulus; Coeffs := f!.coeffs[n mod Modulus + 1];
    return (Coeffs[1] * n + Coeffs[2]) / Coeffs[3];
  end );

#############################################################################
##
#M  ImageElm( <f>, <n> ) . . for semilocal int. rcwa mapping and Z_pi-element
##
##  Image of the element <n> of the ring $\Z_\pi$ for suitable <pi> under the
##  rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "for semilocal integral rcwa mapping and element of Z_pi",
               true, [     IsSemilocalIntegralRcwaMapping 
                       and IsRationalBasedRcwaDenseRep, IsRat ], 0,

  function ( f, n )

    local Coeffs, Modulus;

    if not n in Source(f) then TryNextMethod(); fi;
    Modulus := f!.modulus; Coeffs := f!.coeffs[n mod Modulus + 1];
    return (Coeffs[1] * n + Coeffs[2]) / Coeffs[3];
  end );

#############################################################################
##
#M  ImageElm( <f>, <p> ) . . . . . .  for modular rcwa mapping and polynomial
##
##  Image of the polynomial <p> under the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "for modular rcwa mapping and polynomial",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep,
                       IsPolynomial ], 0,

  function ( f, p )

    local Coeffs, Modulus, r, q, d, x, c, pos;

    if not p in Source(f) then TryNextMethod(); fi;
    Modulus := f!.modulus; r := p mod Modulus;
    q := Size(UnderlyingField(f));
    d := DegreeOfLaurentPolynomial(Modulus);
    x := IndeterminatesOfPolynomialRing(Source(f))[1];
    c := CoefficientsOfUnivariatePolynomial(p);
    pos := Position(AllGFqPolynomialsModDegree(q,d,x),r);
    Coeffs := f!.coeffs[pos];
    return (Coeffs[1] * p + Coeffs[2]) / Coeffs[3];
  end );

#############################################################################
##
#M  \^( <n>, <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
##  Image of the ring element <n> under the rcwa mapping <f>. 
##
InstallMethod( \^,
               "for ring element and rcwa mapping",
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
               "for rcwa mapping and ring element",
               true, [ IsRcwaMapping, IsRingElement ], 0,

  function ( f, n )
    return [ ImageElm( f, n ) ];
  end ); 

#############################################################################
##
#M  ImagesSet( <f>, Integers ) . . . . for integral rcwa mapping and integers
##
##  Image of the rcwa mapping <f>. For classwise constant mappings, only.
##
InstallMethod( ImagesSet,
               "for integral rcwa mapping and integers", true, 
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep,
                 IsIntegers ], 0, 

  function ( f, ints )

    local  c;

    c := f!.coeffs;
    if   not ForAll(c, t -> t[1] = 0) 
    then Info(InfoWarning,1,"The image of ",f," contains at least one full ",
                            "residue class and is not representable as a ",
                            "set in GAP.");
         TryNextMethod();
    else return Set(List([0..f!.modulus-1], n -> n^f));
    fi;
  end );

#############################################################################
##
#M  PreImageElm( <f>, <n> ) . . . for bijective rcwa mapping and ring element
##
##  Preimage of the ring element <n> under the bijective rcwa mapping <f>.
##
InstallMethod( PreImageElm,
               "for bijective rcwa mapping and ring element",
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
               "for integral rcwa mapping and integer", true, 
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep,
                 IsInt ], 0,

  function ( f, n )
    
    local  sol, c, m, n1, pre;

    c := f!.coeffs; m := f!.modulus; sol := [];
    for n1 in [1..m] do
      if c[n1][1] <> 0 then
        pre := (n * c[n1][3] - c[n1][2])/c[n1][1];
        if IsInt(pre) and pre mod m = n1 - 1 then Add(sol,pre); fi;
      else
        if c[n1][2] = n then
          if m = 1 then return Integers; else
            Info(InfoWarning,1,"The set of preimages of ",n," under ",f,
                               " contains at least one full residue class ",
                               "and is not representable as a set in GAP.");
            TryNextMethod();
          fi;
        fi;
      fi;
    od;
    return sol;
  end );

#############################################################################
##
#M  PreImagesRepresentative( <f>, <n> ) . . for int. rcwa mapping and integer
##
##  A representative of the set of preimages of the integer <n> under the
##  integral rcwa mapping <f>. 
##
InstallMethod( PreImagesRepresentative,
               "for integral rcwa mapping and integer", true, 
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep,
                 IsInt ], 0,

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
               "for rcwa mapping and underlying ring", true, 
               [ IsRcwaMapping, IsRing ], 0, 

  function ( f, R )
    if   R = UnderlyingRing( FamilyObj( f ) )
    then return R; else TryNextMethod( ); fi;
  end );

#############################################################################
##
#M  \+( <f>, <g> ) . . . . . . . . . . . for two rational-based rcwa mappings
##
##  Pointwise sum of the rcwa mappings <f> and <g>.
##
InstallMethod( \+,
               "for two rational-based rcwa mappings",
               IsIdenticalObj,
               [IsRationalBasedRcwaMapping and IsRationalBasedRcwaDenseRep,
                IsRationalBasedRcwaMapping and IsRationalBasedRcwaDenseRep],
               0,

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
    then return IntegralRcwaMapping( c3 );
    else pi := NoninvertiblePrimes( Source( f ) );
         return SemilocalIntegralRcwaMapping( pi, c3 );
    fi;
  end );

#############################################################################
##
#M  \+( <f>, <g> ) . . . . . . . . . . . . . .  for two modular rcwa mappings
##
##  Pointwise sum of the rcwa mappings <f> and <g>.
##
InstallMethod( \+,
               "for two modular rcwa mappings",
               IsIdenticalObj,
               [ IsModularRcwaMapping and IsModularRcwaDenseRep,
                 IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,

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

    return ModularRcwaMapping( q, m[3], c[3] );
  end );

#############################################################################
##
#M  AdditiveInverseOp( <f> ) . . . . . . . . . . .  for integral rcwa mapping
##
##  Pointwise additive inverse of rcwa mapping <f>.
##
InstallMethod( AdditiveInverseOp,
               "for integral rcwa mappings", true,
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep ], 0,

  f -> IntegralRcwaMapping( List( f!.coeffs,
                                  c -> [ -c[1], -c[2], c[3] ] ) ) );

#############################################################################
##
#M  AdditiveInverseOp( <f> ) . . . . . .  for semilocal integral rcwa mapping
##
##  Pointwise additive inverse of rcwa mapping <f>.
##
InstallMethod( AdditiveInverseOp,
               "for semilocal integral rcwa mappings",
               true, [     IsSemilocalIntegralRcwaMapping 
                       and IsRationalBasedRcwaDenseRep ], 0,

  f -> SemilocalIntegralRcwaMapping( NoninvertiblePrimes(Source(f)),
                                     List(f!.coeffs,
                                          c -> [ -c[1], -c[2], c[3] ]) ) );

#############################################################################
##
#M  AdditiveInverseOp( <f> ) . . . . . . . . . . . . for modular rcwa mapping
##
##  Pointwise additive inverse of rcwa mapping <f>.
##
InstallMethod( AdditiveInverseOp,
               "for modular rcwa mappings",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,
  
  f -> ModularRcwaMapping( Size(UnderlyingField(f)), f!.modulus,
                           List(f!.coeffs, c -> [ -c[1], -c[2], c[3] ]) ) );

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . .  for two rational-based rcwa mappings
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for two rational-based rcwa mappings",
               IsIdenticalObj,
               [IsRationalBasedRcwaMapping and IsRationalBasedRcwaDenseRep,
                IsRationalBasedRcwaMapping and IsRationalBasedRcwaDenseRep],
               0,

  function ( g, f )

    local c1, c2, c3, m1, m2, m3, n, n1, n2, pi;

    c1 := f!.coeffs;  c2 := g!.coeffs;
    m1 := f!.modulus; m2 := g!.modulus;
    m3 := Lcm( m1, m2 ) * Divisor( f );

    c3 := [];
    for n in [0 .. m3 - 1] do
      n1 := n mod m1 + 1;
      n2 := (c1[n1][1] * n + c1[n1][2])/c1[n1][3] mod m2 + 1;
      Add(c3, [ c1[n1][1] * c2[n2][1],
                c1[n1][2] * c2[n2][1] + c1[n1][3] * c2[n2][2],
                c1[n1][3] * c2[n2][3] ]);
    od;

    if   IsIntegralRcwaMapping( f ) 
    then return IntegralRcwaMapping( c3 );
    else pi := NoninvertiblePrimes( Source( f ) );
         return SemilocalIntegralRcwaMapping( pi, c3 );
    fi;
  end );

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . . . . . . for two modular rcwa mappings
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for two modular rcwa mappings",
               IsIdenticalObj,
               [IsModularRcwaMapping and IsModularRcwaDenseRep,
                IsModularRcwaMapping and IsModularRcwaDenseRep], 100,

  function ( g, f )

    local c, m, d, R, q, x, res, r, n1, n2;

    c := [f!.coeffs, g!.coeffs, []];
    m := [f!.modulus, g!.modulus]; m[3] := Lcm( m[1], m[2] ) * Divisor( f );
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

    return ModularRcwaMapping( q, m[3], c[3] );
  end );

#############################################################################
##
#M  \*( <f>, <g> ) . . . . . . . . . . . . . . . . . .  for two rcwa mappings
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( \*,
               "for two rcwa mappings",
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
               "for rational-based rcwa mappings", true,
               [     IsRationalBasedRcwaMapping 
                 and IsRationalBasedRcwaDenseRep ], 0,
               
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
    then Result := IntegralRcwaMapping( cInv );
    else pi := NoninvertiblePrimes( Source( f ) );
         Result := SemilocalIntegralRcwaMapping( pi, cInv );
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
               "for modular rcwa mappings", true,
               [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,
               
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

    Result := ModularRcwaMapping( q, mInv, cInv );
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
               "for rcwa mappings",
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
               "for two rcwa mappings",
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
               "for rcwa mapping and integer",
               ReturnTrue, [ IsRcwaMapping, IsInt ], 0,

  function ( f, n )
   
    if   n > 1 then TryNextMethod();
    elif n = 1 then return f;
    elif n = 0 then return One( f );
    else            return Inverse( f )^-n; fi;
  end );

#############################################################################
##
#M  IsInjective( <f> ) . . . . . . . . . . .  for rational-based rcwa mapping
##
InstallMethod( IsInjective,
               "for rational-based rcwa mappings", true,
               [     IsRationalBasedRcwaMapping 
                 and IsRationalBasedRcwaDenseRep ], 0,

  function ( f )

    local  c, cInv, m, mInv, n, t, tm, tn, Classes, cl;

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
               "for modular rcwa mappings", true,
               [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,
               
  function ( f )

    local  c, cInv, m, mInv, d, dInv, R, q, x, respols, res, resInv, r, n,
           t, tm, tr, tn, Classes, cl, pos;

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
               "for rational-based rcwa mappings", true,
               [     IsRationalBasedRcwaMapping 
                 and IsRationalBasedRcwaDenseRep ], 0,

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
               "for modular rcwa mappings", true,
               [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,
               
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
                    "for rcwa mappings",
                    true, [ IsRcwaMapping ], 0, IsBijective );

#############################################################################
##
#M  Order( <f> ) . . . . . . . . . . . . . .  for rational-based rcwa mapping
##
##  This method tests whether <f> satisfies one sufficient criterium for
##  having infinite order: it checks whether there is a small, smooth
##  exponent <e> such that <f>^<e> shifts one residue class mod. the modulus
##  non-identically onto itself; in case <f> does not, it gives up.
##
InstallMethod( Order,
               "for rational-based rcwa mappings, arith. progression method",
               true, [     IsRationalBasedRcwaMapping
                       and IsRationalBasedRcwaDenseRep ], 20,

  function ( f )

    local  g, c, m1, m2, exp, e, n, one;

    one := One(f);
    if f = one then return 1; fi;
    if not IsBijective(f) 
    then Error("Order: <rcwa mapping> must be bijective"); fi;
    m1 := f!.modulus; g := f;
    exp := [2,2,3,5,2,7,3,2,11,13,5,3,17,19,2]; e := 1;
    for n in exp do
      c := g!.coeffs; m2 := g!.modulus;
      if m2 > m1 or IsOne(g) then TryNextMethod(); fi;
      if   ForAny([1..m2], n ->     c[n] <> [1,0,1] and c[n]{[1,3]} = [1,1]
                                and c[n][2] mod m2 = 0)
      then Info(RcwaInfo,1,"The ",Ordinal(e)," power of ",f," is ",g,
                           "; this mapping shifts a residue class ",
                           "(modulo ",m2," (its modulus)) non-identically ",
                           "onto itself, hence its order is infinite.");
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
##  This method tries to enumerate orbits of the rcwa mapping <f>.
##  In case <f> has finite order, it may determine it or give up.
##  It also checks whether <f> has an orbit whose length exceeds two times
##  the square of the modulus, and returns `infinity', if so.
##  The validity of this probably sufficient criterium for <f> having
##  infinite order has not yet been proved.
##
InstallMethod( Order,
               "for integral rcwa mappings, cycle method",
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
        Info(RcwaInfo,1,"The mapping ",f," has a cycle longer than 2 times ",
                        "the square of its modulus, hence we claim its ",
                        "order is infinite, although the validity of this ",
                        "criterium has not been proved so far.");
        return infinity;
      fi;
      Add(CycLngs,CycLng);
    od;
    if f^Lcm(CycLngs) = one 
    then return Lcm(CycLngs); else TryNextMethod(); fi;
  end );

############################################################################# 
##
#F  TransitionMatrix( <f>, <deg> ) . . <deg>x<deg>-`Transition matrix' of <f>
##
InstallGlobalFunction( TransitionMatrix,

  function ( f, deg )

    local  T, m, n, i, j;

    m := Modulus(f) * Lcm(deg,Divisor(f));
    T := MutableNullMat(deg,deg);
    for n in [0..m-1] do
      i := n   mod deg;
      j := n^f mod deg;
      T[i+1][j+1] := 1;
    od;
    return T;
  end );

#############################################################################
##
#M  RcwaGraph( <f> ) . . . . . . . . . . . . for rational-based rcwa mapping
##
##  The vertices are labelled by 1..<m> instead of 0..<m>-1 (0 is identified
##  with 1, etc.) because in {\GAP}, permutations cannot move 0. 
##
##  This requires the package `GRAPE' to be loaded.
##
InstallMethod( RcwaGraph,
               "for rational-based rcwa mappings",
               true, [ IsRationalBasedRcwaMapping ], 0,

  function ( f )

    local  m, M;

    if   TestPackageAvailability("grape","4.0") <> true
    then Info(InfoWarning,1,"Sorry, RcwaGraph( <f> ) requires the package ",
                            "grape (4.0 or newer) to be loaded."); fi;
    m := Modulus(f); M := TransitionMatrix(f,m); 
    return Graph(Group(()), [1..m], OnPoints,
                 function(i,j) return M[i][j] = 1; end, true);
  end );

#############################################################################
##
#M  PrimeSet( <f> ) . . . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
InstallMethod( PrimeSet,
               "for rcwa mappings", true, [ IsRcwaMapping ], 0,

  f -> Filtered( Union(Set(Factors(Source(f),Modulus(f))),
                       Set(Factors(Source(f),Multiplier(f))),
                       Set(Factors(Source(f),Divisor(f)))),
                 x -> IsIrreducibleRingElement( Source( f ), x ) ) );

#############################################################################
##
#M  IsTame( <f> ) . . . . . . . . . . . . . . for rational-based rcwa mapping
##
##  This is a probabilistic method.
##
InstallMethod( IsTame,
               "for rational-based rcwa mappings",
               true, [ IsRationalBasedRcwaMapping ], 0,
               
  function ( f )

    local  pow, maxmod, exp, maxexp, m;

    if IsBijective(f) and Order(f) < infinity then return true; fi;
    maxmod := Modulus(f)^2; maxexp := maxmod; exp := 1; pow := f;
    repeat
      pow := pow * pow; m := Modulus(pow); exp := exp * 2;
    until exp > maxexp or m > maxmod;
    if m > maxmod then
      Info(RcwaInfo,1,"The ",Ordinal(exp)," power of ",f," has Modulus ",m,
                      "; this is larger than the square of the modulus of ",
                      "the base, so we claim the mapping is wild, although ",
                      "the validity of this criterium has not yet been ",
                      "proved.");
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
#M  ShortCycles( <f>, <maxlng> ) . .  for rat.-based rcwa mapping and integer
##
InstallMethod( ShortCycles,
               "for rational-based rcwa mappings",
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
               "for tame integral rcwa mappings",
               true, [ IsIntegralRcwaMapping ], 0,
               
  function ( f )

    if not IsTame(f) then TryNextMethod(); fi;
    StandardConjugate(f);
    return CycleType(f);
  end );

#############################################################################
##
#M  StandardConjugate( <f> ) . . .  for integral rcwa mapping of finite order
##
InstallMethod( StandardConjugate,
               "for integral rcwa mappings of finite order", true,
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep ], 0,

  function ( f )

    local  IncreasingLength, CycleSet, RcwaCycles,
           Halved, NonHalved, HalvedLng, NonHalvedLng, NonHalvedByLng, 
           c, m, mf, mStd, d, StdCoeffs, Std, ToStdVals, ToStd,
           ord, pow, cyc, cycs, cyclng, nrcycs, branchpts, branchpos,
           halfcyclng, halfpow, halfpoint, halfpoints,
           cycpreimage1, cycpreimage2, cycimage1, cycimage2, cycimage,
           rescount, imagestart, sigma, l, n, i, j;

    IncreasingLength := function(cyc1,cyc2) 
                          return     Length(cyc1.pts) < Length(cyc2.pts)
                                 or (     Length(cyc1.pts) = Length(cyc2.pts)
                                      and cyc1.pts < cyc2.pts );
                        end;

    CycleSet := function ( cycs )

      local  cycsbuf, cyc;

      cycsbuf := ShallowCopy(cycs); cycs := [];
      for cyc in cycsbuf do
        if   not    Set(List(cyc.pts, n -> n mod m)) 
                 in List(cycs, cyc -> Set(List(cyc.pts, n -> n mod m)))
        then Add(cycs,cyc); fi;
      od;
      return cycs;
    end;

    if   IsOne(f) 
    then SetStandardizingConjugator(f,One(f));
         SetCycleType(f,[[],[]]);
         return f;
    fi;
    if not IsBijective(f) then TryNextMethod(); fi;
    ord := Order(f); if ord = infinity then TryNextMethod(); fi;
    Info(RcwaInfo,2,"StandardConjugate for ",f);
    c := Coefficients(f);
    d := Divisor(f); mf := Modulus(Group(f)); m := d * mf;
    RcwaCycles := [];
    for cyclng in DivisorsInt(ord) do
      pow  := f^cyclng;
      cycs := List(FixedClassesOfRcwaMapping(pow,m), n -> Cycle(f,n));
      for i in [1..Length(cycs)] do
        if   Length(cycs[i]) < cyclng 
        then cycs[i] := Cycle(f,cycs[i][1] + m); fi;
      od;
      RcwaCycles := Concatenation(RcwaCycles,
                                  List(cycs,cyc->rec(pts      := cyc,
                                                     HalvedAt := fail)));
      if cyclng mod 2 = 0 then
        halfcyclng := cyclng/2;
        halfpow    := f^halfcyclng;
        halfpoints := FixedPointsOfRcwaMapping(halfpow,m);
        for i in [1..Length(cycs)] do
          halfpoint := Filtered(halfpoints,
                                n1 -> n1 mod m in List(cycs[i],
                                                       n2 -> n2 mod m));
          Assert(1,Length(halfpoint) <= 1);
          if   halfpoint <> []
          then RcwaCycles[   Length(RcwaCycles)
                           - Length(cycs) + i].HalvedAt := halfpoint[1];
          fi;
        od;
      fi;
    od;
    RcwaCycles := CycleSet(RcwaCycles);
    Halved     := Filtered(RcwaCycles, cyc -> cyc.HalvedAt <> fail);
    NonHalved  := Difference(RcwaCycles,Halved);
    Sort(Halved,IncreasingLength); Sort(NonHalved,IncreasingLength);
    NonHalved := List(NonHalved, cyc -> cyc.pts);
    Info(RcwaInfo,2,"A set of representatives for the series of ",
                    "`halved' cycles is ",Halved,".");
    Info(RcwaInfo,2,"A set of representatives for the series of ",
                    "`non-halved' cycles is ",NonHalved,".");
    HalvedLng      := List(Halved, cyc -> Length(cyc.pts));
    NonHalvedLng   := Set(List(NonHalved,Length));
    NonHalvedByLng := List(NonHalvedLng,
                           l -> Filtered(NonHalved, cyc -> Length(cyc) = l));
    SetCycleType(f,[HalvedLng,NonHalvedLng]);
    Info(RcwaInfo,2,"The cycle type is ",CycleType(f),".");
    StdCoeffs := []; rescount := 0;
    for cyc in Halved do
      l := Length(cyc.pts);
      for i in [1..l/2 - 1] do Add(StdCoeffs,[1,1,1]); od;
      Add(StdCoeffs,[-1, 2 * rescount + l/2 - 1, 1]); 
      rescount := rescount + l/2;
    od;
    for cyc in NonHalvedByLng do
      l := Length(cyc[1]);
      for j in [1..l - 1] do Add(StdCoeffs,[1,1,1]); od;
      Add(StdCoeffs,[1,-l + 1,1]);
    od;
    Std  := RcwaMapping(StdCoeffs);
    if Std = f then
      Info(RcwaInfo,2,"The mapping is already in standard form.");
      SetStandardizingConjugator(f,IdentityIntegralRcwaMapping);
      return Std;
    fi;
    mStd := Modulus(Std); ToStdVals := []; rescount := 0;
    for cyc in Halved do
      l := Length(cyc.pts);
      cycimage1 := [rescount..rescount + l/2 - 1];
      cycimage2 := Concatenation([rescount-mStd..rescount-mStd + l/2 - 1],
                                 [rescount+mStd..rescount+mStd + l/2 - 1]);
      cycpreimage1 := Cycle(f,cyc.HalvedAt);
      cycpreimage2 := cyc.pts;
      ToStdVals := Concatenation(ToStdVals,
                     List([1..l/2],i->[cycpreimage1[i],cycimage1[i]]),
                     List([1..l  ],i->[cycpreimage2[i],cycimage2[i]]));
      rescount := rescount + l/2;
    od;
    for i in [1..Length(NonHalvedByLng)] do
      branchpts := Filtered([0..mf - 1],
                            k -> c[k mod Modulus(f) + 1][3] > 1);
      branchpos := List(NonHalvedByLng[i],
                        cyc -> List(cyc, n -> n mod mf in branchpts));
      for j in [2..Length(NonHalvedByLng[i])] do
        if branchpos[j] <> branchpos[1] then
          cyc   := NonHalvedByLng[i][j];
          sigma := SortingPerm(Concatenation([2..Length(cyc)],[1]));
          while List(cyc, n -> n mod mf in branchpts) <> branchpos[1] do
            cyc := Permuted(cyc,sigma);
            if cyc = NonHalvedByLng[i][j] then break; fi;
          od;
          NonHalvedByLng[i][j] := cyc;
        fi;
      od;
    od;
    Info(RcwaInfo,3,"The `non-halved' cycles as they are mapped to ",
                    "cycles of\nthe standard conjugate:\n",
                    NonHalvedByLng,".");
    for cycs in NonHalvedByLng do
      l := Length(cycs[1]); nrcycs := Length(cycs);
      cycimage := [rescount..rescount + l - 1];
      for i in [1..nrcycs] do
        cycpreimage1 := cycs[i];
        cycpreimage2 := Cycle(f,cycs[i][1] + m);
        ToStdVals := Concatenation(ToStdVals,
                       List([1..l],j->[cycpreimage1[j], cycimage[j] 
                                    + (i - 1) * mStd]),
                       List([1..l],j->[cycpreimage2[j], cycimage[j] 
                                    + (i + nrcycs - 1) * mStd]));
      od;
      rescount := rescount + l;
    od;
    Info(RcwaInfo,2,"[Preimage, image] - pairs defining a standardizing ",
                    "conjugator are ",ToStdVals,".");
    ToStd := RcwaMapping(m,ToStdVals);
    Assert(1,f^ToStd = Std);
    SetStandardizingConjugator(f,ToStd);
    return Std;
  end );

#############################################################################
##
#M  StandardizingConjugator( <f> ) . . . . . . . .  for integral rcwa mapping
##
InstallMethod( StandardizingConjugator,
               "for integral rcwa mappings of finite order",
               true, [ IsIntegralRcwaMapping ], 0,

  function ( f )

    StandardConjugate(f);
    return StandardizingConjugator(f);
  end );

#############################################################################
##
#M  IsConjugate( RCWA( Integers ), <f>, <g> ) 
##
##  For integral rcwa mappings, in the full group `RCWA( Integers )'.
##  Checks whether the standard conjugates of <f> and <g> are equal, if the
##  mappings are tame, and looks for different lengths of short cycles
##  otherwise (the latter will not terminate if <f> and <g> are conjugate).
##
InstallOtherMethod( IsConjugate,
                    "for two integral rcwa mappings, in RCWA(Z)",
                    true, 
                    [ IsNaturalRCWA_Z, 
                      IsIntegralRcwaMapping, IsIntegralRcwaMapping ], 0,

  function ( RCWA_Z, f, g )

    local  maxlng;

    if f = g then return true; fi;
    if Order(f) <> Order(g) or IsTame(f) <> IsTame(g) then return false; fi;
    if IsTame(f) then
      return StandardConjugate(f) = StandardConjugate(g);
    else
      maxlng := 2;
      repeat
        if    Collected(List(ShortCycles(f,maxlng),Length))
           <> Collected(List(ShortCycles(g,maxlng),Length))
        then return false; fi;
        maxlng := maxlng * 2;
      until false;
    fi;
  end );

#############################################################################
##
#M  IsConjugate( RCWA( Z_pi( <pi> ) ), <f>, <g> ) 
##
##  For semilocal integral rcwa mappings, in the full group
##  `RCWA( Z_pi( <pi> ) )'. Probabilistic method.
##
InstallOtherMethod( IsConjugate,
                   "for two semilocal integral rcwa mappings, in RCWA(Z_pi)",
                    ReturnTrue, 
                    [ IsNaturalRCWA_Z_pi,
                      IsSemilocalIntegralRcwaMapping,
                      IsSemilocalIntegralRcwaMapping ], 0,

  function ( RCWA_Z_pi, f, g )

    local  maxlng;

    if not f in RCWA_Z_pi or not g in RCWA_Z_pi then return fail; fi;
    if f = g then return true; fi;
    if Order(f) <> Order(g) or IsTame(f) <> IsTame(g) then return false; fi;
    maxlng := 2;
    repeat
      if    Collected(List(ShortCycles(f,maxlng),Length))
         <> Collected(List(ShortCycles(g,maxlng),Length))
      then return false; fi;
      maxlng := maxlng * 2;
    until false;
  end );

#############################################################################
##
#E  rcwamap.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
