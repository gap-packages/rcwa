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
##  the ring of integers and its semilocalizations:
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
##  A semilocal integral rcwa mapping object <f> (here, the underlying ring
##  is $\Z_{(\pi)}$ for a set of primes $\pi$) stores the same information.
##  The ring which <f> acts on can be accessed as `Source(<f>)'.
##
##  Some remarks concerning the implementation of rcwa mappings of
##  GF(<q>)[<x>] (modular rcwa mappings):
## 
##  A modular rcwa mapping object <f> also stores the modulus <modulus> and
##  a coefficients list <coeffs>.
##  The meaning of <modulus> and <coeffs> is completely analogous to the
##  above, where the residue classes for <coeffs> are sorted according to
##  the default order of their smallest-degree representatives in {\GAP}.
##  The ring which <f> acts on can again be accessed as `Source(<f>)'.
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
    then return SemilocalIntegralRcwaMappingsFamily(NoninvertiblePrimes(R));
    elif IsUnivariatePolynomialRing( R ) and IsFiniteFieldPolynomialRing( R )
    then return ModularRcwaMappingsFamily( Size( CoefficientsRing( R ) ),
                IndeterminateNumberOfLaurentPolynomial(Representative(R)) );
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

    local Result, R, fam;

    if IsInt(pi) then pi := [pi]; fi;
    R   := Z_pi( pi );
    fam := SemilocalIntegralRcwaMappingsFamily( R );
    Result := Objectify( NewType(    fam,
                                     IsSemilocalIntegralRcwaMapping
                                 and IsRationalBasedRcwaDenseRep ),
                         rec( coeffs  := coeffs,
                              modulus := Length(coeffs) ) );
    SetSource(Result, R ); SetRange (Result, R );
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

    local  Result, R, fam, ind;

    ind := IndeterminateNumberOfLaurentPolynomial( coeffs[1][1] );
    R   := PolynomialRing( GF( q ), [ ind ] );
    fam := ModularRcwaMappingsFamily( R );
    Result := Objectify( NewType( fam, IsModularRcwaMapping
                                   and IsModularRcwaDenseRep ),
                         rec( coeffs  := coeffs,
                              modulus := modulus ) );
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

    local  d, x, P, p, quiet;

    quiet := ValueOption("BeQuiet") = true;
    if not (    IsPosInt(q) and IsPrimePowerInt(q) 
            and IsPolynomial(modulus) and IsList(coeffs)
            and ForAll(coeffs, c -> Length(c) = 3) 
            and ForAll(Flat(coeffs), IsPolynomial)
            and Length(Set(List(Flat(coeffs),
                                IndeterminateNumberOfLaurentPolynomial)))=1)
    then if quiet then return fail; fi;
         Error("usage: ModularRcwaMapping( <q>, <modulus>, <coeffs> )\n",
               "where <q> is the size of the coefficients field, ",
               "<modulus> is an element of\nits underlying ring and ",
               "<coeffs> is a suitable coefficients list.\n");
    fi;
    d   := DegreeOfLaurentPolynomial(modulus);
    x   := IndeterminateOfLaurentPolynomial(coeffs[1][1]);
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
               "RCWA: for integral rcwa mappings", true,
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
               "RCWA: for semilocal integral rcwa mappings",
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
               "RCWA: for modular rcwa mappings",
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
#M  PrintObj( <f> ) . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( PrintObj,
               "RCWA: for integral rcwa mappings", true,
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep ], 0,

  function ( f )
    Print( "IntegralRcwaMapping( ", f!.coeffs, " )" );
  end );

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . for semilocal integral rcwa mapping
##
InstallMethod( PrintObj,
               "RCWA: for semilocal integral rcwa mappings",
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
               "RCWA: for modular rcwa mappings",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,

  function ( f )
    Print( "ModularRcwaMapping( ", Size(UnderlyingField(f)),
           ", ", f!.modulus, ", ", f!.coeffs, " )" );
  end );

#############################################################################
##
#M  ViewObj( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
InstallMethod( ViewObj,
               "RCWA: for rational-based and modular rcwa mappings",
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
               "RCWA: for rational-based and modular rcwa mappings",
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
#M  LaTeXObj( <f> ) . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( LaTeXObj,
               "RCWA: for integral rcwa mappings", true,
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
               "RCWA: for two rational-based rcwa mappings",
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
               "RCWA: for two modular rcwa mappings",
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
               "RCWA: for two rcwa mappings",
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
               "RCWA: for integral rcwa mappings", true,
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep ], 0,
               f -> ZeroIntegralRcwaMapping );

#############################################################################
##
#M  ZeroOp( <f> ) . . . . . . . . . . . . for semilocal integral rcwa mapping
##
##  Zero rcwa mapping.
##
InstallMethod( ZeroOp,
               "RCWA: for semilocal integral rcwa mappings",
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
               "RCWA: for modular rcwa mappings",
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
               "RCWA: for rcwa mappings", true, [ IsRcwaMapping ], 0,
               f -> f!.coeffs = [ [ 0, 0, 1 ] ] * One( Source( f ) ) );  

#############################################################################
##
#M  OneOp( <f> ) . . . . . . . . . . . . . . . . .  for integral rcwa mapping
##
##  Identity rcwa mapping.
##
InstallMethod( OneOp,
               "RCWA: for integral rcwa mappings", true,
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep ], 0,
               f -> IdentityIntegralRcwaMapping );

#############################################################################
##
#M  OneOp( <f> ) . . . . . . . . . . . .  for semilocal integral rcwa mapping
##
##  Identity rcwa mapping.
##
InstallMethod( OneOp,
               "RCWA: for semilocal integral rcwa mappings",
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
               "RCWA: for modular rcwa mappings",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,

  function ( f )

    local  one;
 
    one := ModularRcwaMappingNC( Size(UnderlyingField(f)), One(Source(f)),
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
               "RCWA: for rcwa mappings", true, [ IsRcwaMapping ], 0,
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
                    "RCWA: for rcwa mappings",
                    true, [ IsRcwaMapping ], 0, f -> f!.coeffs );

#############################################################################
##
#M  Modulus( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
InstallMethod( Modulus,
               "RCWA: for rcwa mappings",
               true, [ IsRcwaMapping ], 0, f -> f!.modulus );

#############################################################################
##
#M  Multiplier( <f> ) . . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
InstallMethod( Multiplier,
               "RCWA: for rcwa mappings", true, [ IsRcwaMapping ], 0,
               f -> Lcm( List( f!.coeffs, c -> c[1] ) ) );

#############################################################################
##
#M  Multiplier( <f> ) . . . . . . . . . . for semilocal integral rcwa mapping
##
InstallMethod( Multiplier,
               "RCWA: for semilocal integral rcwa mappings",
               true, [     IsSemilocalIntegralRcwaMapping
                       and IsRationalBasedRcwaDenseRep ], 10,

  f -> Lcm( List( f!.coeffs,
                  c -> StandardAssociate( Source( f ), c[1] ) ) ) );

#############################################################################
##
#M  Divisor( <f> ) . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
InstallMethod( Divisor,
               "RCWA: for rcwa mappings",
               true, [ IsRcwaMapping ], 0,
               f -> Lcm( List( f!.coeffs, c -> c[ 3 ] ) ) );

#############################################################################
##
#M  Multpk( <f>, <p>, <k> ) . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( Multpk,
               "RCWA: for integral rcwa mappings",
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
#M  IsFlat( <f> ) . . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( IsFlat,
               "RCWA: for integral rcwa mappings",
               true, [     IsIntegralRcwaMapping
                       and IsRationalBasedRcwaDenseRep ], 0,

  f -> IsSubset( [-1,1], Set( Flat( List( f!.coeffs, c -> c{[1,3]} ) ) ) ) );

#############################################################################
##
#M  IsFlat( <f> ) . . . . . . . . . . . . for semilocal integral rcwa mapping
##
InstallMethod( IsFlat,
               "RCWA: for semilocal integral rcwa mappings",
               true, [ IsSemilocalIntegralRcwaMapping ], 10,
               f -> [ Multiplier(f), Divisor(f) ] = [ 1, 1 ] );

#############################################################################
##
#M  IsFlat( <f> ) . . . . . . . . . . . . . . . . .  for modular rcwa mapping
##
InstallMethod( IsFlat,
               "RCWA: for modular rcwa mappings",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,
               f ->  ForAll( Flat( List( f!.coeffs, c -> c{ [ 1, 3 ] } ) ),
                             p -> DegreeOfLaurentPolynomial( p ) = 0 ) );

#############################################################################
##
#M  IsBalanced( <f> ) . . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
InstallMethod( IsBalanced,
               "RCWA: for rcwa mappings", true, [ IsRcwaMapping ], 0,

  f -> Set( Factors( Multiplier( f ) ) ) = Set( Factors( Divisor( f ) ) ) );

#############################################################################
##
#M  IsClassWiseOrderPreserving( <f> ) . . . for "rational-based" rcwa mapping
##
InstallMethod( IsClassWiseOrderPreserving,
               "RCWA: for rational-based rcwa mappings",
               true, [     IsRationalBasedRcwaMapping 
                       and IsRationalBasedRcwaDenseRep ], 0,
               f -> ForAll( f!.coeffs, c -> c[ 1 ] >= 0 ) );

#############################################################################
##
#M  MovedPoints( <f> ) . . . . . . . . . . . . . . for bijective rcwa mapping
##
##  The set of moved points (support) of the bijective rcwa mapping <f>.
##
InstallOtherMethod( MovedPoints,
                    "RCWA: for bijective rcwa mapping", true,
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
               "RCWA: for integral rcwa mapping and integer",
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
##  Image of the element <n> of the ring $\Z_{(\pi)}$ for suitable <pi> under
##  the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "RCWA: for semilocal integral rcwa mapping and el. of Z_pi",
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
               "RCWA: for modular rcwa mapping and polynomial",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep,
                       IsPolynomial ], 0,

  function ( f, p )

    local Coeffs, Modulus, F, FList, r, q, d, x, c, pos;

    if not p in Source(f) then TryNextMethod(); fi;
    Modulus := f!.modulus; r := p mod Modulus;
    F := UnderlyingField(f); q := Size(F);
    d := DegreeOfLaurentPolynomial(Modulus);
    x := IndeterminatesOfPolynomialRing(Source(f))[1];
    c := CoefficientsOfUnivariatePolynomial(r);
    c := Concatenation(c,ListWithIdenticalEntries(d-Length(c),Zero(F)));
    FList := AsList(F); c := List(c,ci->Position(FList,ci)-1);
    pos := Sum(List([1..d],i->c[i]*q^(i-1))) + 1;
    Coeffs := f!.coeffs[pos];
    return (Coeffs[1] * p + Coeffs[2]) / Coeffs[3];
  end );

#############################################################################
##
#M  \^( <n>, <f> ) . . . . . . . . . . . .  for ring element and rcwa mapping
##
##  Image of the ring element <n> under the rcwa mapping <f>. 
##
InstallMethod( \^,
               "RCWA: for ring element and rcwa mapping",
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
               "RCWA: for rcwa mapping and ring element",
               true, [ IsRcwaMapping, IsRingElement ], 0,

  function ( f, n )
    return [ ImageElm( f, n ) ];
  end ); 

#############################################################################
##
#M  ImagesSet( <f>, Integers ) . . . . for integral rcwa mapping and integers
##
##  Image of the rcwa mapping <f>.
##
InstallMethod( ImagesSet,
               "RCWA: for integral rcwa mapping and integers", true, 
               [ IsRationalBasedRcwaMapping, IsRing ], 0, 

  function ( f, R )

    if R <> Source( f ) then TryNextMethod( ); fi;
    return Union( ImagesSet( f, ResidueClass( R, 2, 0 ) ),
                  ImagesSet( f, ResidueClass( R, 2, 1 ) ) );
  end );

#############################################################################
##
#M  ImagesSet( <f>, <S> ) . . for integral rcwa map. and union of residue cl.
##
##  Image of the set <S> under the rcwa mapping <f>.
##
InstallMethod( ImagesSet,
               "RCWA: for integral rcwa mapping and residue class union",
               true, [ IsIntegralRcwaMapping, IsUnionOfResidueClassesOfZ ],
               0,

  function ( f, S )

    local  image, immod, imres, rump, c, m, mult, preim, r, excluded, im, n;

    c := Coefficients(f); m := Modulus(f);
    if   ForAll( c, t -> t[1] = 0 )
    then mult := 0;
    else mult := Lcm( List( Filtered( c, t1 -> t1[1]<>0 ), t2 -> t2[1] ) );
    fi;
    rump  := ResidueClassUnion( Integers, Modulus(S), Residues(S) );
    immod := m * mult * Modulus(S);
    preim := Filtered( [0..immod*Divisor(f)-1], n -> c[n mod m + 1][1]<>0 );
    imres := Set( List( Intersection( rump, preim ), n -> n^f mod immod ) );
    image := Union( ResidueClassUnion( Integers, immod, imres ),
                    List( IncludedElements(S), n -> n^f ) );
    for r in [ 0 .. m - 1 ] do
      if c[ r + 1 ][ 1 ] = 0 then
        if   Intersection( S, ResidueClass( Integers, m, r ) ) <> [ ]
        then image := Union( image, [ c[ r + 1 ][ 2 ] ] ); fi;
      fi;
    od;
    excluded := ExcludedElements(S);
    for n in excluded do
      im := n^f;
      if   Intersection( S, PreImagesElm( f, im ) ) = []
      then image := Difference( image, [ im ] ); fi;
    od;
    return image;
  end );

#############################################################################
##
#M  \^( <S>, <f> ) . . . . . . . . . . . . . . . . . for set and rcwa mapping
##
##  Image of the set <S> under the rcwa mapping <f>.
##  In particular, <S> can be a union of residue classes.
##
InstallOtherMethod( \^,
                    "RCWA: for set and rcwa mapping",
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
               "RCWA: for bijective rcwa mapping and ring element",
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
               "RCWA: for integral rcwa mapping and integer", true, 
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep,
                 IsInt ], 0,

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
               "RCWA: for integral rcwa mapping and integer", true, 
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
               "RCWA: for rcwa mapping and underlying ring", true, 
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
                    "RCWA: for rcwa map. and list of elements of its range",
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
               "RCWA: for integral rcwa mapping and residue class union",
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
               "RCWA: for two rational-based rcwa mappings",
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
    then return IntegralRcwaMappingNC( c3 );
    else pi := NoninvertiblePrimes( Source( f ) );
         return SemilocalIntegralRcwaMappingNC( pi, c3 );
    fi;
  end );

#############################################################################
##
#M  \+( <f>, <g> ) . . . . . . . . . . . . . .  for two modular rcwa mappings
##
##  Pointwise sum of the rcwa mappings <f> and <g>.
##
InstallMethod( \+,
               "RCWA: for two modular rcwa mappings",
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

    return ModularRcwaMappingNC( q, m[3], c[3] );
  end );

#############################################################################
##
#M  AdditiveInverseOp( <f> ) . . . . . . . . . . .  for integral rcwa mapping
##
##  Pointwise additive inverse of rcwa mapping <f>.
##
InstallMethod( AdditiveInverseOp,
               "RCWA: for integral rcwa mappings", true,
               [ IsIntegralRcwaMapping and IsRationalBasedRcwaDenseRep ], 0,

  f -> IntegralRcwaMappingNC( List( f!.coeffs,
                                    c -> [ -c[1], -c[2], c[3] ] ) ) );

#############################################################################
##
#M  AdditiveInverseOp( <f> ) . . . . . .  for semilocal integral rcwa mapping
##
##  Pointwise additive inverse of rcwa mapping <f>.
##
InstallMethod( AdditiveInverseOp,
               "RCWA: for semilocal integral rcwa mappings",
               true, [     IsSemilocalIntegralRcwaMapping 
                       and IsRationalBasedRcwaDenseRep ], 0,

  f -> SemilocalIntegralRcwaMappingNC( NoninvertiblePrimes(Source(f)),
                                       List(f!.coeffs,
                                            c -> [ -c[1], -c[2], c[3] ]) ) );

#############################################################################
##
#M  AdditiveInverseOp( <f> ) . . . . . . . . . . . . for modular rcwa mapping
##
##  Pointwise additive inverse of rcwa mapping <f>.
##
InstallMethod( AdditiveInverseOp,
               "RCWA: for modular rcwa mappings",
               true, [ IsModularRcwaMapping and IsModularRcwaDenseRep ], 0,
  
  f -> ModularRcwaMappingNC( Size(UnderlyingField(f)), f!.modulus,
                             List(f!.coeffs, c -> [-c[1],-c[2],c[3]]) ) );

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ) . .  for two rational-based rcwa mappings
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "RCWA: for two rational-based rcwa mappings",
               IsIdenticalObj,
               [IsRationalBasedRcwaMapping and IsRationalBasedRcwaDenseRep,
                IsRationalBasedRcwaMapping and IsRationalBasedRcwaDenseRep],
               SUM_FLAGS,

  function ( g, f )

    local c1, c2, c3, m1, m2, m3, n, n1, n2, pi;

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

    if   IsIntegralRcwaMapping( f ) 
    then return IntegralRcwaMappingNC( c3 );
    else pi := NoninvertiblePrimes( Source( f ) );
         return SemilocalIntegralRcwaMappingNC( pi, c3 );
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
               "RCWA: for two modular rcwa mappings",
               IsIdenticalObj,
               [IsModularRcwaMapping and IsModularRcwaDenseRep,
                IsModularRcwaMapping and IsModularRcwaDenseRep], SUM_FLAGS,

  function ( g, f )

    local c, m, d, R, q, x, res, r, n1, n2;

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

    return ModularRcwaMappingNC( q, m[3], c[3] );
  end );

#############################################################################
##
#M  \*( <f>, <g> ) . . . . . . . . . . . . . . . . . .  for two rcwa mappings
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( \*,
               "RCWA: for two rcwa mappings",
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
               "RCWA: for rational-based rcwa mappings", true,
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
    then Result := IntegralRcwaMappingNC( cInv );
    else pi := NoninvertiblePrimes( Source( f ) );
         Result := SemilocalIntegralRcwaMappingNC( pi, cInv );
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
               "RCWA: for modular rcwa mappings", true,
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

    Result := ModularRcwaMappingNC( q, mInv, cInv );
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
               "RCWA: for rcwa mappings",
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
               "RCWA: for two rcwa mappings",
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
               "RCWA: for rcwa mapping and integer",
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
               "RCWA: for rational-based rcwa mappings", true,
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
               "RCWA: for modular rcwa mappings", true,
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
               "RCWA: for rational-based rcwa mappings", true,
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
               "RCWA: for modular rcwa mappings", true,
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
                    "RCWA: for rcwa mappings",
                    true, [ IsRcwaMapping ], 0, IsBijective );

#############################################################################
##
#M  Order( <f> ) . . . . . . . . . . . . . . . . . . . . . . for rcwa mapping
##
##  The `factors of multiplier and divisor' criterion.
##
InstallMethod( Order,
               "RCWA: for rcwa mappings, factors of mult. and div. - crit.",
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
##  exponent <e> such that <f>^<e> shifts one residue class mod. the modulus
##  non-identically onto itself; in case <f> does not, it gives up.
##
InstallMethod( Order,
               "RCWA: for rat.-based rcwa map's, arith. progression method",
               true, [     IsRationalBasedRcwaMapping
                       and IsRationalBasedRcwaDenseRep ], 20,

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
                           " is ",g,"; this mapping shifts the residue ",
                           "class ",r-1," mod ",m2," non-identically ",
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
               "RCWA: for integral rcwa mappings, cycle method",
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
#F  TransitionMatrix( <f>, <deg> ) . . <deg>x<deg>-`Transition matrix' of <f>
##
InstallGlobalFunction( TransitionMatrix,

  function ( f, deg )

    local  T, m, n, i, j;

    if   not IsRationalBasedRcwaMapping(f) or not IsPosInt(deg)
    then Error("usage: TransitionMatrix( <f>, <deg> ),\nwhere <f> is a ",
               "rational-based rcwa mapping and <deg> is an integer > 0.\n");
    fi;
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
#M  TransitionGraph( <f>, <m> ) . . . . . . . for rational-based rcwa mapping
##
##  The vertices are labelled by 1..<m> instead of 0..<m>-1 (0 is identified
##  with 1, etc.) because in {\GAP}, permutations cannot move 0.
##
##  The result is returned as a GRAPE graph.
##
InstallMethod( TransitionGraph,
               "RCWA: for rational-based rcwa mappings",
               true, [ IsRationalBasedRcwaMapping, IsPosInt ], 0,

  function ( f, m )

    local  M;

    M := TransitionMatrix(f,m); 
    return Graph(Group(()), [1..m], OnPoints,
                 function(i,j) return M[i][j] = 1; end, true);
  end );

#############################################################################
##
#M  OrbitsModulo( <f>, <m> ) . . . . . . . .  for rational-based rcwa mapping
##
InstallMethod( OrbitsModulo,
               "RCWA: for rational-based rcwa mappings", true,
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
               "RCWA: for rational-based rcwa mappings", true,
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
            and (   val in Source(f) and cond = "stop"
                 or IsPosInt(val) and cond = "length"))
    then Error("for usage of `Trajectory' see manual.\n"); fi;
    seq := [n];
    if cond = "length" then
      for step in [1..val-1] do Add(seq,seq[step]^f); od;
    elif cond = "stop" then
      repeat Add(seq,seq[Length(seq)]^f); until seq[Length(seq)] = val;
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
               "RCWA: for rcwa mappings", true, [ IsRcwaMapping ], 0,

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
               "RCWA: for bijective rcwa mappings", true, [ IsRcwaMapping ],
               100,

  function ( f )

    local  R, mult, div;

    if IsFlat(f)
    then Info(InfoRCWA,4,"IsTame: mapping is flat, hence tame.");
         return true; fi;
    if not IsBijective(f) then TryNextMethod(); fi;
    Info(InfoRCWA,1,"IsTame:`factors of multiplier and divisor' criterion.");
    R := Source(f); mult := Multiplier(f); div := Divisor(f);
    if   Set(Factors(R,mult)) <> Set(Factors(R,div))
    then return false; else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  IsTame( <f> ) . . . . . . . . . . . . . . . .  for bijective rcwa mapping
##
##  The `dead end' criterion.
##  This is only applicable for bijective mappings.
##
InstallMethod( IsTame,
               "RCWA: for bijective rcwa mappings", true,
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
    then return false; else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  IsTame( <f> ) . . . . . . . . . . . . . . . . . . . . .  for rcwa mapping
##
##  The `finite order or flat power' criterion.
##
InstallMethod( IsTame,
               "RCWA: for rcwa mappings", true,
               [ IsRcwaMapping ], 30,

  function ( f )

    local  pow, exp, e;

    Info(InfoRCWA,2,"IsTame:`finite order or flat power' criterion.");
    if IsBijective(f) and Order(f) <> infinity then return true; fi;
    pow := f; exp := [2,2,3,5,2,7,3,2,11,13,5,3,17,19,2]; e := 1;
    for e in exp do
      pow := pow^e;
      if IsFlat(pow) then return true; fi;
      if   IsRationalBasedRcwaMapping(f) and Modulus(pow) > 6 * Modulus(f)
        or     IsModularRcwaMapping(f)
           and   DegreeOfLaurentPolynomial(Modulus(pow))
               > DegreeOfLaurentPolynomial(Modulus(f)) + 2
      then TryNextMethod(); fi;
    od;
  end );

#############################################################################
##
#M  IsTame( <f> ) . . . . . . . . . . . . . . for rational-based rcwa mapping
##
##  This is a probabilistic method.
##
InstallMethod( IsTame,
               "RCWA: for rational-based rcwa mappings",
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
                    "RCWA: for rational-based rcwa mapping and ring element",
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
               "RCWA: for rational-based rcwa mappings",
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
#M  RespectedClassPartition( <sigma> ) . . .  for tame bijective rcwa mapping
##
InstallMethod( RespectedClassPartition,
               "RCWA: for tame bijective rcwa mappings", true,
               [ IsRcwaMapping ], 0,

  function ( sigma )

    local  R, m, moved, fixed, G, pcp, untouched, cls, cl, orb, r, i;

    if not (IsBijective(sigma) and IsTame(sigma)) then return fail; fi;
    R := Source(sigma); m := Modulus(sigma);
    moved := MovedPoints(sigma);
    if   IsUnionOfResidueClasses(moved) and Modulus(moved) <> One(R)
    then fixed := Residues(Complement(moved));
    elif moved <> [] then fixed := []; else fixed := [0]; fi;
    pcp := List(fixed,i->ResidueClass(R,m,i));
    untouched := Difference(AllResidues(R,m),fixed);
    G := Group(sigma);
    while untouched <> [] do
      i := untouched[1]; RemoveSet(untouched,i);
      cls := Difference(ResidueClass(R,m,i),Union(pcp));
      if cls <> [] then
        for r in Residues(cls) do
          cl := ResidueClass(R,Modulus(cls),r);
          orb := Orbit(G,cl); pcp := Union(pcp,orb);
        od;
      fi;
    od;
    Assert(1,Union(pcp)=R);
    Assert(2,Action(G,pcp)<>fail);
    return pcp;
  end );

#############################################################################
##
#M  FlateningConjugator( <sigma> ) . for tame bijective integral rcwa mapping
##
InstallMethod( FlateningConjugator,
               "RCWA: for tame bijective integral rcwa mappings", true,
               [ IsIntegralRcwaMapping ], 0,

  function ( sigma )

    local  pcp, c, m, mtilde, r, rtilde, cl, m_cl, i, j;

    if IsFlat(sigma) then return One(sigma); fi;
    pcp := RespectedClassPartition(sigma); 
    if pcp = fail then return fail; fi;
    m := Lcm(List(pcp,Modulus)); mtilde := Length(pcp);
    c := List([1..m],i->[1,0,1]);
    for rtilde in [0..mtilde-1] do
      cl := pcp[rtilde+1];
      r := Residues(cl)[1]; m_cl := Modulus(cl);
      for j in [0..m/m_cl-1] do
        c[j*m_cl+r+1] := [mtilde,m_cl*rtilde-mtilde*r,m_cl];
      od;
    od;
    return RcwaMapping(c);
  end );

#############################################################################
##
#M  FlatConjugate( <f> ) . . . . . . . . . . . . . . .  for tame rcwa mapping
##
InstallMethod( FlatConjugate,
               "RCWA: for tame rcwa mappings", true, [ IsRcwaMapping ], 0,
               f -> f^FlateningConjugator( f ) );

#############################################################################
##
#M  StandardizingConjugator( <sigma> ) .  for tame bij. integral rcwa mapping
##
InstallMethod( StandardizingConjugator,
               "RCWA: for tame bijective integral rcwa mappings", true,
               [ IsIntegralRcwaMapping ], 0,

  function ( sigma )

    local  toflat, flat, m, mtilde, mTilde, r, rtilde, c, pcp, cycs, lngs,
           cohorts, cohort, l, nrcycs, res, cyc, n, ntilde, i, j, k;

    if not (IsBijective(sigma) and IsTame(sigma)) then return fail; fi;
    if not IsFlat(sigma) then
      toflat := FlateningConjugator(sigma);
      flat   := sigma^toflat;
    else toflat := One(sigma); flat := sigma; fi;
    m := Modulus(flat); pcp := RespectedClassPartition(flat);
    cycs := Cycles(flat,pcp); lngs := Set(List(cycs,Length));
    cohorts := List(lngs,l->Filtered(cycs,cyc->Length(cyc)=l));
    mtilde := Sum(lngs); c := List([1..m],i->[1,0,1]); rtilde := 0;
    for cohort in cohorts do
      nrcycs := Length(cohort); l := Length(cohort[1]);
      res := List([1..l],i->List([1..nrcycs],j->Residues(cohort[j][i])[1]));
      cyc := List([1..nrcycs],j->Cycle(flat,res[1][j]));
      mTilde := nrcycs * mtilde;
      for i in [1..l] do
        for r in res[i] do
          j := Position(res[i],r);
          n := cyc[j][i]; ntilde := (j-1)*mtilde+rtilde;
          k := (ntilde*m-mTilde*n-m*rtilde+mtilde*r)/(m*mtilde);
          c[r+1] := [mTilde,k*m*mtilde+m*rtilde-mtilde*r,m];
        od;
        rtilde := rtilde + 1;
      od;
    od; 
    return toflat * RcwaMapping(c);
  end );

#############################################################################
##
#M  StandardConjugate( <f> ) . . . . . . . . . . . . .  for tame rcwa mapping
##
InstallMethod( StandardConjugate,
               "RCWA: for tame rcwa mappings", true, [ IsRcwaMapping ], 0,
               f -> f^StandardizingConjugator( f ) );

#############################################################################
##
#M  CycleType( <f> ) . . . . . . . . . . . . . for tame integral rcwa mapping
##
InstallMethod( CycleType,
               "RCWA: for tame integral rcwa mappings",
               true, [ IsIntegralRcwaMapping ], 0,
               
  function ( f )

    if not IsTame(f) then TryNextMethod(); fi;
    StandardConjugate(f);
    return CycleType(f);
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
                    "RCWA: for two integral rcwa mappings, in RCWA(Z)",
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
                   "RCWA: for two semiloc. int. rcwa mappings in RCWA(Z_pi)",
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
#M  ContractionCentre( <f>, <maxn>, <maxlng> ) . .  for integral rcwa mapping
##
InstallMethod( ContractionCentre,
               "RCWA: for integral rcwa mappings", true,
               [ IsIntegralRcwaMapping, IsPosInt, IsPosInt ], 0,

  function ( f, maxn, maxlng )

    local  S0, n, n_i, i, seq;

    if not IsIntegralRcwaMapping(f) or IsBijective(f) then return fail; fi;
    S0 := [];
    for n in Integers do
      seq := []; n_i := n;
      for i in [1..maxlng] do
        if n_i in S0 then break; fi;
        if   n_i in seq
        then S0 := Union(S0,Trajectory(f,n_i,n_i,"stop")); break; fi;
        Add(seq,n_i);
        n_i := n_i^f;
        if   i = maxlng
        then Info(InfoWarning,1,"Length limit exceeded, start value ",n); fi;
      od;
      if n >= maxn then break; fi;
    od;
    return S0;
  end );

#############################################################################
##
#M  Restriction( <g>, <f> ) . . . . . . . . . . .  for integral rcwa mappings
##
InstallMethod( Restriction,
               "RCWA: for integral rcwa mappings", true,
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
    return gf;
  end );

#############################################################################
##
#E  rcwamap.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here





