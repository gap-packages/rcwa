#############################################################################
##
#W  rcwamap.gi                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains implementations of methods and functions for
##  computing with residue class-wise affine mappings of the ring of
##  integers.
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
##  An rcwa mapping object <f> just stores the modulus <modulus> and a
##  coefficients list <coeffs>.
##  The list <coeffs> consists of <modulus> lists of length 3, where
##  <coeffs>[<a> + 1]> gives the coefficients of the mapping on the residue
##  class <a> mod <modulus>, hence if <n> mod <modulus> = <a>, we have 
##  $$
##    <n>^<f> = (<coeffs>[<a> + 1][1] * <n> + <coeffs>[<a> + 1][2]) /
##               <coeffs>[<a> + 1][3]>.
##  $$
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

InstallTrueMethod( IsMapping, IsIntegralRcwaMapping );

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
  SetCoefficientsOfRcwaMapping(f,f!.coeffs);
  SetModulusOfRcwaMapping(f,f!.modulus);
end;
MakeReadOnlyGlobal( "ReduceIntegralRcwaMapping" );

#############################################################################
##
#F  IntegralRcwaMapping( <coeffs> )
#F  IntegralRcwaMapping( <perm>, <range> )
#F  IntegralRcwaMapping( <modulus>, <val> )
#F  RcwaMapping( <coeffs> )
#F  RcwaMapping( <perm>, <range> )
#F  RcwaMapping( <modulus>, <val> )
##
InstallGlobalFunction( IntegralRcwaMapping,

  function ( arg )

    local Coeffs, Perm, PermRange, Val, min, max, m, n, r, pts, Result,
          quiet;

    quiet := ValueOption("BeQuiet") = true;
    if   Length(arg) = 1 
    then Coeffs := arg[1];
         if not (IsList(Coeffs) and ForAll(Flat(Coeffs),IsInt)
                 and ForAll(Coeffs, IsList)
                 and ForAll(Coeffs, c -> Length(c) = 3)
                 and ForAll([0..Length(Coeffs) - 1],
                            n -> Coeffs[n + 1][3] <> 0 and
                                 (n * Coeffs[n + 1][1] + Coeffs[n + 1][2])
                                 mod Coeffs[n + 1][3] = 0 and
                                 (  (n + Length(Coeffs)) * Coeffs[n + 1][1] 
                                  +  Coeffs[n + 1][2])
                                 mod Coeffs[n + 1][3] = 0))
         then if quiet then return fail; fi;
              Error("the coefficients ",Coeffs," do not define a proper ",
                    "integral rcwa mapping.\n");
         fi;
    elif IsPerm(arg[1]) and IsRange(arg[2])
    then Perm := arg[1]; PermRange := arg[2];
         if   Permutation(Perm,PermRange) = fail
         then if quiet then return fail; fi;
              Error("the permutation ",Perm," does not act on the range ",
                    PermRange,".\n");
         fi;
         min := Minimum(PermRange); max := Maximum(PermRange);
         m := max - min + 1; Coeffs := [];
         for n in [min..max] do
           r := n mod m + 1;
           Coeffs[r] := [1, n^Perm - n, 1];
         od;
    elif IsPosInt(arg[1]) and IsList(arg[2])
         and Set(List(arg[2],Length)) = [2] and ForAll(Flat(arg[2]),IsInt)
    then
      m := arg[1]; Val := Set(arg[2]); Coeffs := [];
      for r in [1..m] do
        pts := Filtered(Val, pt -> pt[1] mod m = r - 1);
        if   Length(pts) < 2 
        then if quiet then return fail; fi;
             Error("the mapping is not given at at least 2 points <n> ",
                   "with <n> mod ",m," = ",r - 1,".\n");
        fi;
        Coeffs[r] := [  pts[1][2] - pts[2][2],
                        pts[1][2] * (pts[1][1] - pts[2][1])
                      - pts[1][1] * (pts[1][2] - pts[2][2]),
                        pts[1][1] - pts[2][1]];
      od;
    else if quiet then return fail; fi;
         Error("see RCWA Manual for usage of IntegralRcwaMapping.\n");
    fi;
    Result := Objectify( NewType(    IntegralRcwaMappingsFamily,
                                     IsIntegralRcwaMapping
                                 and IsIntegralRcwaDenseRep ),
                         rec( coeffs  := Coeffs,
                              modulus := Length(Coeffs) ) );
    SetSource(Result, Integers);
    SetRange (Result, Integers);
    ReduceIntegralRcwaMapping(Result);
    if   IsBound(Val) 
    then if not ForAll(Val, t -> t[1]^Result = t[2])
         then if quiet then return fail; fi;
              Error("the values ",Val," do not define a proper integral ",
                    "rcwa mapping.\n"); 
         fi;
    fi;
    return Result;
  end );

#############################################################################
##
#V  ZeroIntegralRcwaMapping . . . . . . . . . . .  zero integral rcwa mapping
##
InstallValue( ZeroIntegralRcwaMapping,
              IntegralRcwaMapping( [ [ 0, 0, 1 ] ] ) );

#############################################################################
##
#V  IdentityIntegralRcwaMapping . . . . . . .  identity integral rcwa mapping
##
InstallValue( IdentityIntegralRcwaMapping,
              IntegralRcwaMapping( [ [ 1, 0, 1 ] ] ) );

#############################################################################
##
#M  ZeroOp( <f> ) . . . . . . . . . . . . . . . . . for integral rcwa mapping
##
##  Zero rcwa mapping.
##
InstallMethod( ZeroOp,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,
               f -> ZeroIntegralRcwaMapping ); 

#############################################################################
##
#M  OneOp( <f> ) . . . . . . . . . . . . . . . . .  for integral rcwa mapping
##
##  Identity rcwa mapping.
##
InstallMethod( OneOp,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,
               f -> IdentityIntegralRcwaMapping );

############################################################################# 
## 
#M  IsOne( <f> ) . . . . . . . . . . . . . . . . .  for integral rcwa mapping 
## 
##  <f> = identity rcwa mapping ? 
## 
InstallMethod( IsOne, 
               "for integral residue class-wise affine mappings", 
               true, [ IsIntegralRcwaMapping ], 0, 
               f -> f = One( f ) );  

#############################################################################
##
#M  Coefficients( <f> ) . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallOtherMethod( Coefficients,
                    "for integral residue class-wise affine mappings",
                    true, [     IsIntegralRcwaMapping
                            and IsIntegralRcwaDenseRep ], 0,
                    f -> f!.coeffs );

#############################################################################
##
#M  Modulus( <f> ) . . . . . . . . . . . . . . . .  for integral rcwa mapping
##
InstallMethod( Modulus,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,
               f -> f!.modulus );

#############################################################################
##
#M  Multiplier( <f> ) . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( Multiplier,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,
               f -> AbsInt( Lcm( List( f!.coeffs, c -> c[ 1 ] ) ) ) );

#############################################################################
##
#M  Divisor( <f> ) . . . . . . . . . . . . . . . .  for integral rcwa mapping
##
InstallMethod( Divisor,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,
               f -> AbsInt( Lcm( List( f!.coeffs, c -> c[ 3 ] ) ) ) );

#############################################################################
##
#M  IsFlat( <f> ) . . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( IsFlat,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping ], 0, 
               f -> Multiplier( f ) = 1 and Divisor( f ) = 1 );

#############################################################################
##
#M  IsClassWiseOrderPreserving( <f> ) . . . . . . . for integral rcwa mapping
##
InstallMethod( IsClassWiseOrderPreserving,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,
               f -> ForAll( f!.coeffs, c -> c[ 1 ] >= 0 ) );

DisplayAffineMapping := function ( t )

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
MakeReadOnlyGlobal( "DisplayAffineMapping" );

#############################################################################
##
#M  PrintObj( <f> ) . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( PrintObj,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,

  function ( f )
    Print( "IntegralRcwaMapping( ", f!.coeffs, " )" );
  end );

#############################################################################
##
#M  ViewObj( <f> ) . . . . . . . . . . . . . . . .  for integral rcwa mapping
##
InstallMethod( ViewObj,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,

  function ( f )

    local  m, c;

    m := f!.modulus; c := f!.coeffs;
    if   f = One (f) 
         then Print("<identity integral rcwa mapping>");
    elif f = Zero(f) 
         then Print("<zero integral rcwa mapping>");
    elif m = 1 and c[1][1] = 0
         then Print("<constant integral rcwa mapping with value ",
                    c[1][2],">");
    else Print("<");
         if   HasIsBijective(f) and IsBijective(f) 
         then Print("bijective ");
         elif HasIsInjective(f) and IsInjective(f)
         then Print("injective ");
         elif HasIsSurjective(f) and IsSurjective(f)
         then Print("surjective ");
         fi;
         Print("integral rcwa mapping");
         if m = 1 then
           Print(": n -> ");
           DisplayAffineMapping(c[1]);
         else
           Print(" with modulus ",m);
           if HasOrder(f) then Print(", of order ",Order(f)); fi;
         fi;
         Print(">");
    fi;
  end );

#############################################################################
##
#M  Display( <f> ) . . . . . . . . . . . . . . . .  for integral rcwa mapping
##
##  Display the rcwa mapping <f> as a nice, human-readable table.
##
InstallMethod( Display,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,

  function ( f )

    local  m, c, name, poses, pos, t, i, str, mdec;

    m := f!.modulus; c := f!.coeffs;
    if HasName(f) then name := Name(f); else name := "f"; fi;
    if   f = One (f) 
         then Print("Identity integral rcwa mapping\n");
    elif f = Zero(f) 
         then Print("Zero integral rcwa mapping\n");
    elif m = 1 and c[1][1] = 0
         then Print("Constant integral rcwa mapping with value ",
                    c[1][2],"\n");
    else if m > 1 then Print("\n"); fi;
         if   HasIsBijective(f) and IsBijective(f)
         then Print("Bijective i");
         elif HasIsInjective(f) and IsInjective(f)
         then Print("Injective i");
         elif HasIsSurjective(f) and IsSurjective(f)
         then Print("Surjective i");
         else Print("I");
         fi;
         Print("ntegral rcwa mapping");
         if m = 1 then
           Print(": n -> ");
           DisplayAffineMapping(c[1]);
           Print("\n");
         else
           Print(" with modulus ",m);
           if HasOrder(f) then Print(", of order ",Order(f)); fi;
           Print("\n\n");
           mdec := Length(String(m));
           Print( "               n mod ", m, String(" ",40 - 21 - mdec),
                  "|              ",name,"(n)              \n",
                  "----------------------------------------+",
                  "---------------------------------" ); 
           poses := AsSortedList(List(Set(c),
                                      t -> Filtered([0 .. m - 1],
                                                    i -> c[i + 1] = t)));
           for pos in poses do
             str := " "; 
             for i in pos do
               Append(str,String(i,mdec + 1));
               if Length(str) >= 39 - mdec then
                 Print("\n",str,String(" ",40 - Length(str)),"| ");
                 str := " ";
               fi;
             od;
             if   str <> " " 
             then Print("\n",str,String(" ",40 - Length(str)),"| "); fi;
             DisplayAffineMapping(c[pos[1] + 1]);
           od;
           Print("\n\n");
         fi;
    fi;
  end );

#############################################################################
##
#M  \=( <f>, <g> ) . . . . . . . . . . . . . . . . for integral rcwa mappings
##
InstallMethod( \=,
               "for two integral residue class wise affine mappings",
               IsIdenticalObj,
               [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep,
                 IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ],
               0,

  function ( f, g )
    return f!.coeffs = g!.coeffs;
  end );

#############################################################################
##
#M  \<( <f>, <g> ) . . . . . . . . . . . . . . . . for integral rcwa mappings
##
##  Total ordering of rcwa maps (for tech. purposes, only).
##
InstallMethod( \<,
               "for two integral residue class wise affine mappings",
               IsIdenticalObj,
               [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep,
                 IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ],
               0,

  function ( f, g )
    return f!.coeffs < g!.coeffs;
  end );

#############################################################################
##
#M  ImageElm( <f>, <n> ) . . . . . . .  for integral rcwa mapping and integer
##
##  Image of the integer <n> under the rcwa mapping <f>. 
##
InstallMethod( ImageElm,
               "for integral residue class-wise affine mapping and integer",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep,
                       IsInt ], 0,

  function ( f, n )

    local Coeffs, Modulus;

    Modulus := f!.modulus; Coeffs := f!.coeffs[n mod Modulus + 1];
    return (Coeffs[1] * n + Coeffs[2]) / Coeffs[3];
  end );

#############################################################################
##
#M  \^( <n>, <f> ) . . . . . . . . . .  for integer and integral rcwa mapping
##
##  Image of the integer <n> under the rcwa mapping <f>. 
##
InstallMethod( \^,
               "for an integer and a residue class wise affine mapping",
               ReturnTrue,
               [ IsInt,
                 IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ],
               0,

  function ( n, f )
    return ImageElm( f, n );
  end );

############################################################################# 
## 
#M  ImagesElm( <f>, <n> ) . . . . . . . for integral rcwa mapping and integer 
## 
##  Images of the integer <n> under the rcwa mapping <f>.
##  For technical purposes, only.
## 
InstallMethod( ImagesElm, 
               "for integral residue class-wise affine mapping and integer", 
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep, 
                       IsInt ], 0, 
 
  function ( f, n ) 
 
    local Coeffs, Modulus; 
 
    Modulus := f!.modulus; Coeffs := f!.coeffs[n mod Modulus + 1]; 
    return [(Coeffs[1] * n + Coeffs[2]) / Coeffs[3]]; 
  end ); 

#############################################################################
##
#M  ImagesSet( <f>, Integers ) . . . . for integral rcwa mapping and integers
##
##  Image of the rcwa mapping <f>. For classwise constant mappings, only.
##
InstallMethod( ImagesSet,
               "for integral rcwa mapping and integers", true, 
               [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep,
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
#M  PreImageElm( <f>, <n> ) . for bijective integral rcwa mapping and integer 
## 
##  Preimage of the integer <n> under the bijective rcwa mapping <f>.  
## 
InstallMethod( PreImageElm, 
               "for bijective integral rcwa mapping and integer", 
               true, [ IsIntegralRcwaMapping and IsBijective, 
                       IsInt ], 0, 
 
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
               [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep,
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
               [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep,
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
#M  PreImagesSet( <f>, Integers ) . .  for integral rcwa mapping and integers
##
##  Preimage of the rcwa mapping <f>. For technical purposes, only.
##
InstallMethod( PreImagesSet,
               "for integral rcwa mapping and integers", true, 
               [ IsIntegralRcwaMapping, IsIntegers ], 0, 

  function ( f, ints )
    return Integers;
  end );

#############################################################################
##
#M  \^( <g>, <h> ) . . . . . . . . . . . . . . for two integral rcwa mappings
##
##  Conjugate of the rcwa mapping <g> under <h>.
##
InstallMethod( \^,
               "for two residue class wise affine mappings",
               IsIdenticalObj,
               [ IsIntegralRcwaMapping, IsIntegralRcwaMapping ], 0,

  function ( g, h )

    local  f;

    f := h^-1 * g * h;
    if HasOrder (g) then SetOrder (f,Order (g)); fi;
    if HasIsTame(g) then SetIsTame(f,IsTame(g)); fi;
    return f;
  end );

#############################################################################
##
#M  \+( <f>, <g> ) . . . . . . . . . . . . . . for two integral rcwa mappings
##
##  Pointwise sum of the rcwa mappings <f> and <g>.
##
InstallMethod( \+,
               "for two integral residue class wise affine mappings",
               IsIdenticalObj,
               [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep,
                 IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ],
               0,

  function ( f, g )
    
    local c1, c2, c3, m1, m2, m3, n, n1, n2, Result;

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

    Result := IntegralRcwaMapping( c3 );

    return Result;
  end );

#############################################################################
##
#M  AdditiveInverseOp( <f> ) . . . . . . . . . . .  for integral rcwa mapping
##
##  Pointwise additive inverse of rcwa mapping <f>.
##
InstallMethod( AdditiveInverseOp,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,
               
  function ( f )

    local  Coeffs, NegCoeffs;

    Coeffs    := f!.coeffs;
    NegCoeffs := List(Coeffs, c -> [ -c[1], -c[2], c[3] ] );

    return IntegralRcwaMapping( NegCoeffs );
  end );

#############################################################################
##
#M  CompositionMapping2( <g>, <f> ). . . . . . for two integral rcwa mappings
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( CompositionMapping2,
               "for two integral residue class wise affine mappings",
               IsIdenticalObj,
               [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep,
                 IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ],
               0,

  function ( g, f )
    
    local c1, c2, c3, m1, m2, m3, n, n1, n2, Result;

    c1 := f!.coeffs;  c2 := g!.coeffs;
    m1 := f!.modulus; m2 := g!.modulus;
    m3 := Lcm(m1, m2) * Lcm(List([1 .. m1], n -> c1[n][3]));

    c3 := [];
    for n in [0 .. m3 - 1] do
      n1 := n mod m1 + 1;
      n2 := (c1[n1][1] * n + c1[n1][2])/c1[n1][3] mod m2 + 1;
      Add(c3, [ c1[n1][1] * c2[n2][1],
                c1[n1][2] * c2[n2][1] + c1[n1][3] * c2[n2][2],
                c1[n1][3] * c2[n2][3] ]);
    od;

    Result := IntegralRcwaMapping( c3 );

    return Result;
  end );

#############################################################################
##
#M  \*( <f>, <g> ) . . . . . . . . . . . . . . for two integral rcwa mappings
##
##  Product (composition) of the rcwa mappings <f> and <g>.
##  The mapping <f> is applied first.
##
InstallMethod( \*,
               "for two residue class wise affine mappings",
               IsIdenticalObj, [ IsRcwaMapping, IsRcwaMapping ], 0,

  function ( f, g )
    return CompositionMapping( g, f );
  end );

#############################################################################
##
#M  InverseOp( <f> ) . . . . . . . . . . . . . . .  for integral rcwa mapping
##
##  Inverse mapping of bijective rcwa mapping <f>.
##
InstallMethod( InverseOp,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,
               
  function ( f )

    local  Result, c, cInv, m, mInv, n, t, tm, tn, Classes, cl;

    c := f!.coeffs; m := f!.modulus;
    cInv := [];
    mInv := AbsInt(   Lcm(List(c, t -> t[1])) 
                    * m / Gcd(m, Gcd(List(c, t -> t[3]))));
    for n in [1 .. m] do
      t := [c[n][3], -c[n][2], c[n][1]]; if t[3] = 0 then return fail; fi;
      tm := AbsInt(c[n][1]) * m / Gcd(m, c[n][3]);
      tn := ((n - 1) * c[n][1] + c[n][2]) / c[n][3] mod tm;
      Classes := List([1 .. mInv/tm], i -> (i - 1) * tm + tn);
      for cl in Classes do
        if IsBound(cInv[cl + 1]) and cInv[cl + 1] <> t then return fail; fi; 
        cInv[cl + 1] := t;
      od;
    od;

    if not ForAll([1..mInv], i -> IsBound(cInv[i])) then return fail; fi;

    Result := IntegralRcwaMapping( cInv );
    SetInverse(f, Result);
    SetInverse(Result, f);
    if HasOrder(f) then SetOrder(Result, Order(f)); fi;

    return Result;
  end );

#############################################################################
##
#M  InverseGeneralMapping( <f> ) . . . . . . . . .  for integral rcwa mapping
##
##  Inverse mapping of bijective rcwa mapping <f>.
##
InstallMethod( InverseGeneralMapping,
               "for integral residue class-wise affine mappings", true, 
               [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,
              
  function ( f )

    if IsBijective(f) then return Inverse(f); else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  \^( <f>, <n> ) . . . . . . . . . .  for integral rcwa mapping and integer
##
##  <n>-th power of the rcwa mapping <f>. 
##  This method is for faster handling of the case of a negative exponent
##  if the inverse of <f> already has been computed.
##
InstallMethod( \^,
               "for residue class wise affine mapping and integer",
               ReturnTrue,
               [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep, 
                 IsInt ], 0,

  function ( f, n )
   
    if   n > 1 then TryNextMethod();
    elif n = 1 then return f;
    elif n = 0 then return IdentityIntegralRcwaMapping;
    else            return Inverse(f)^-n; fi;
  end );

#############################################################################
##
#M  IsInjective( <f> ) . . . . . . . . . . . . . .  for integral rcwa mapping
##
InstallMethod( IsInjective,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,

  function ( f )

    local  c, cInv, m, mInv, n, t, tm, tn, Classes, cl;

    c := f!.coeffs; m := f!.modulus;
    cInv := [];
    mInv := AbsInt(   Lcm(List(c, t -> t[1])) 
                    * m / Gcd(m, Gcd(List(c, t -> t[3]))));
    for n in [1 .. m] do
      t := [c[n][3], -c[n][2], c[n][1]]; if t[3] = 0 then return false; fi;
      tm := AbsInt(c[n][1]) * m / Gcd(m, c[n][3]);
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
#M  IsSurjective( <f> ) . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( IsSurjective,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,

  function ( f )

    local  c, cInv, m, mInv, n, t, tm, tn, Classes, cl;

    c := f!.coeffs; m := f!.modulus;
    cInv := [];
    if ForAll(c, t -> t[1] = 0) then return false; fi;
    mInv := AbsInt(   Lcm(Filtered(List(c, t -> t[1]), k -> k <> 0)) 
                    * m / Gcd(m, Gcd(List(c, t -> t[3]))));
    for n in [1 .. m] do
      t := [c[n][3], -c[n][2], c[n][1]];
      if t[3] <> 0 then
        tm := AbsInt(c[n][1]) * m / Gcd(m, c[n][3]);
        tn := ((n - 1) * c[n][1] + c[n][2]) / c[n][3] mod tm;
        Classes := List([1 .. mInv/tm], i -> (i - 1) * tm + tn);
        for cl in Classes do cInv[cl + 1] := t; od;
      fi;
    od;
    if   ForAll([1..mInv], i -> IsBound(cInv[i])) 
    then return true; 
    else return false; fi;
  end );

#############################################################################
##
#M  IsUnit( <f> ) . . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallOtherMethod( IsUnit,
                    "for integral residue class-wise affine mappings",
                    true, [ IsIntegralRcwaMapping ], 0, IsBijective );

#############################################################################
##
#M  Order( <f> ) . . . . . . . . . . . . . . . . .  for integral rcwa mapping
##
##  This method tests whether <f> satisfies one sufficient criterium for
##  having infinite order: it checks whether there is a small, smooth
##  exponent <e> such that <f>^<e> shifts one residue class mod. the modulus
##  non-identically onto itself; in case <f> does not, it gives up.
##
InstallMethod( Order,
               "for integral rcwa mappings, arithmetic progression method",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ],
               20,

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
      if m2 > m1 or g = One(g) then TryNextMethod(); fi;
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
#M  RcwaGraphAdjacencyMatrix( <f> ) . . . . . . . . for integral rcwa mapping
##
##  The vertices are labelled by 1..<m> instead of 0..<m>-1 (0 is identified
##  with 1, etc.) because in {\GAP}, lists cannot be indexed by 0. 
##
InstallMethod( RcwaGraphAdjacencyMatrix,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,

  function ( f )

    local  M, BaseRange, c, m, n, i, j;

    c := f!.coeffs; m := f!.modulus;
    BaseRange := [0 .. m * Lcm(List([1 .. m], r -> c[r][3])) - 1];
    M := MutableNullMat(m,m);
    for n in BaseRange do
      i := n mod m + 1; j := n^f mod m + 1;
      M[i][j] := M[i][j] + 1;
    od;

    return M;
  end );

#############################################################################
##
#M  RcwaGraph( <f> ) . . . . . . . . . . . . . . .  for integral rcwa mapping
##
##  The vertices are labelled by 1..<m> instead of 0..<m>-1 (0 is identified
##  with 1, etc.) because in {\GAP}, permutations cannot move 0. 
##
##  This requires the package `grape' to be loaded.
##
InstallMethod( RcwaGraph,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping ], 0,

  function ( f )

    local  M, m;

    if   TestPackageAvailability("grape","4.0") <> true
    then Info(InfoWarning,1,"Sorry, RcwaGraph( <f> ) requires the package ",
                            "grape (4.0 or newer) to be loaded."); fi;
    M := RcwaGraphAdjacencyMatrix(f); m := Modulus(f);
    return Graph(Group(()), [1..m], OnPoints,
                 function(i,j) return M[i][j] <> 0; end, true);
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
#M  PrimeSet( <f> ) . . . . . . . . . . . . . . . . for integral rcwa mapping
##
InstallMethod( PrimeSet,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,

  function ( f )

    local  c, m;

    c := f!.coeffs; m := f!.modulus;
    return Difference(Set(Factors(m * Lcm(Flat(List(c, t -> t{[1, 3]}))))),
                      [ 1 ]);
  end );

#############################################################################
##
#M  IsTame( <f> ) . . . . . . . . . . . . . . . . . for integral rcwa mapping
##
##  This is a probabilistic method.
##
InstallMethod( IsTame,
               "for integral rcwa mappings",
               true, [ IsIntegralRcwaMapping ], 0,
               
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
         if   IsInt(fp) and fp mod m = r - 1 
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
#M  ShortCycles( <f>, <maxlng> ) . . .  for integral rcwa mapping and integer
##
InstallMethod( ShortCycles,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping, IsPosInt ], 0,

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
               "for integral rcwa mappings of finite order",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,

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

    if   f = One(f) 
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
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,

  function ( f )

    StandardConjugate(f);
    return StandardizingConjugator(f);
  end );

#############################################################################
##
#M  IsConjugate( RCWA( Integers ), <f>, <g> ) 
##
##  For tame integral rcwa mappings, in the full group `RCWA( Integers )'.
##  Checks whether the standard conjugates of <f> and <g> are equal.
##
InstallOtherMethod( IsConjugate,
                    "for two rcwa mappings of finite order, in RCWA(Z)",
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
#M  Variation( <f> ) . . . . . . . . . . . . . . .  for integral rcwa mapping
##
InstallMethod( Variation,
               "for integral residue class-wise affine mappings",
               true, [ IsIntegralRcwaMapping and IsIntegralRcwaDenseRep ], 0,

  function ( f )

    local  c, m;

    c := f!.coeffs; m := f!.modulus;
    return   Sum(List([1 .. m],
                      i -> AbsInt(   c[i          ][1]/c[i          ][3] 
                                   - c[i mod m + 1][1]/c[i mod m + 1][3])))
           * 1 / (2 * m);
  end );

#############################################################################
##
#E  rcwamap.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
