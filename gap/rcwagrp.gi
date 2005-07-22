#############################################################################
##
#W  rcwagrp.gi                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains implementations of methods and functions for computing
##  with rcwa groups over the ring of integers, its semilocalizations and
##  over polynomial rings in one variable over a finite field.
##
##  See the definitions given in the files `rcwamap.gd' and `rcwagrp.gd'.
##
Revision.rcwagrp_gi :=
  "@(#)$Id$";

# A few auxiliary functions.

GeneratorsAndInverses :=
  G->Concatenation(GeneratorsOfGroup(G),List(GeneratorsOfGroup(G),g->g^-1));
MakeReadOnlyGlobal( "GeneratorsAndInverses" );

EpimorphismByGenerators := function ( F, G )
  return GroupHomomorphismByImages(F,G,GeneratorsOfGroup(F),
                                       GeneratorsOfGroup(G));
end;
MakeReadOnlyGlobal( "EpimorphismByGenerators" );

EpimorphismByGeneratorsNC := function ( F, G )
  return GroupHomomorphismByImagesNC(F,G,GeneratorsOfGroup(F),
                                         GeneratorsOfGroup(G));
end;
MakeReadOnlyGlobal( "EpimorphismByGeneratorsNC" );

# Some implications.

InstallTrueMethod( IsGroup,     IsRcwaGroup );
InstallTrueMethod( IsRcwaGroup, IsRationalBasedRcwaGroup );
InstallTrueMethod( IsRationalBasedRcwaGroup, IsIntegralRcwaGroup );
InstallTrueMethod( IsRationalBasedRcwaGroup,
                   IsSemilocalIntegralRcwaGroup );
InstallTrueMethod( IsRcwaGroup, IsModularRcwaGroup );

#############################################################################
##
#M  IsGeneratorsOfMagmaWithInverses( <l> ) .  for list of integral rcwa map's
##
##  Tests whether all rcwa mappings in the list <l> belong to the same
##  family and are bijective, hence generate a group.
##
InstallMethod( IsGeneratorsOfMagmaWithInverses,
               "for lists of rcwa mappings (RCWA)", true,
               [ IsListOrCollection ], 0,

  function ( l )

    if   ForAll(l,IsRcwaMapping)
    then return     Length(Set(List(l,FamilyObj))) = 1
                and ForAll(l,IsBijective); 
    else TryNextMethod(); fi;
  end );

#############################################################################
## 
#M  IsCyclic( <G> ) . . . . . . . . . . . . . . . . generic method for groups
## 
InstallMethod( IsCyclic, "generic method for groups (RCWA)", true,
               [ IsGroup ], 50,

  function ( G )

    if   Length(GeneratorsOfGroup(G)) = 1
    then return true;
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#V  TrivialIntegralRcwaGroup( <G> ) . . . . . . . trivial integral rcwa group
#V  TrivialRcwaGroup( <G> )
##
InstallValue( TrivialIntegralRcwaGroup,
              Group( IdentityIntegralRcwaMapping ) );

#############################################################################
##
#M  TrivialSubmagmaWithOne( <G> ). . . . . . . . . . . . . . . for rcwa group
##
InstallMethod( TrivialSubmagmaWithOne,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  Triv;

    Triv := Group(One(G));
    SetParentAttr(Triv,G);
    return Triv;
  end );

#############################################################################
##
#V  IntegralRcwaGroupsFamily . . . . . the family of all integral rcwa groups
##
BindGlobal( "IntegralRcwaGroupsFamily",
            FamilyObj( TrivialIntegralRcwaGroup ) );

#############################################################################
##
#M  RCWACons( IsRcwaGroup, Integers ) . . . . . . . . . . . . . . . RCWA( Z )
##
##  Group formed by all bijective integral rcwa mappings.
##
InstallMethod( RCWACons,
               "natural RCWA(Z) (RCWA)", true,
               [ IsRcwaGroup, IsIntegers ], 0,

  function ( filter, R )

    local  G;

    G := Objectify( NewType( IntegralRcwaGroupsFamily,
                             IsIntegralRcwaGroup and IsAttributeStoringRep ),
                    rec( ) );
    SetIsTrivial( G, false );
    SetOne( G, IdentityIntegralRcwaMapping );
    SetIsNaturalRCWA_Z( G, true );
    SetModulusOfRcwaGroup( G, 0 );
    SetMultiplier( G, infinity );
    SetDivisor( G, infinity );
    SetIsFinite( G, false ); SetSize( G, infinity );
    SetIsFinitelyGeneratedGroup( G, false );
    SetCentre( G, TrivialIntegralRcwaGroup );
    SetIsAbelian( G, false );
    SetIsSolvableGroup( G, false );
    SetIsPerfectGroup( G, false );
    SetIsSimpleGroup( G, false );
    SetRepresentative( G, RcwaMapping( [ [ -1, 0, 1 ] ] ) );
    SetName( G, "RCWA(Z)" );
    return G;
  end );

#############################################################################
##
#M  RCWACons( IsRcwaGroup, Z_pi( <pi> ) ) . . . . . . . . . . .  RCWA( Z_pi )
##
##  Group formed by all bijective rcwa mappings over $\Z_{(\pi)}$.
##
InstallMethod( RCWACons,
               "natural RCWA(Z_pi) (RCWA)", true, [ IsRcwaGroup, IsZ_pi ], 0,

  function ( filter, R )

    local  G, pi, id;

    pi := NoninvertiblePrimes( R );
    id := RcwaMapping( pi, [ [1,0,1] ] );
    G  := Objectify( NewType( FamilyObj( Group( id ) ),
                                  IsSemilocalIntegralRcwaGroup
                              and IsAttributeStoringRep ),
                     rec( ) );
    SetIsTrivial( G, false );
    SetOne( G, id );
    SetIsNaturalRCWA_Z_pi( G, true );
    SetModulusOfRcwaGroup( G, 0 );
    SetMultiplier( G, infinity );
    SetDivisor( G, infinity );
    SetIsFinite( G, false ); SetSize( G, infinity );
  # SetIsFinitelyGeneratedGroup( G, false ); ???
    SetCentre( G, Group( id ) );
    SetIsAbelian( G, false );
    SetIsSolvableGroup( G, false );
    SetRepresentative( G, -id );
    SetName( G, Concatenation( "RCWA(", Name(R), ")" ) );
    return G;
  end );

#############################################################################
##
#M  RCWACons( IsRcwaGroup, PolynomialRing( GF( <q> ), 1 ) )  RCWA( GF(q)[x] )
##
##  Group formed by all bijective rcwa mappings over GF(q)[x].
##
InstallMethod( RCWACons,
               "natural RCWA(Z_pi) (RCWA)", true, 
               [ IsRcwaGroup, IsUnivariatePolynomialRing ], 0,

  function ( filter, R )

    local  G, q, id;

    q  := Size( CoefficientsRing( R ) );
    id := RcwaMapping( q, One(R), [ [1,0,1] * One(R) ] );
    G  := Objectify( NewType( FamilyObj( Group( id ) ),
                                  IsModularRcwaGroup
                              and IsAttributeStoringRep ),
                     rec( ) );
    SetIsTrivial( G, false );
    SetOne( G, id );
    SetIsNaturalRCWA_GF_q_x( G, true );
    SetModulusOfRcwaGroup( G, Zero( R ) );
    SetMultiplier( G, infinity );
    SetDivisor( G, infinity );
    SetIsFinite( G, false ); SetSize( G, infinity );
    SetIsFinitelyGeneratedGroup( G, false );
    SetCentre( G, Group( id ) );
    SetIsAbelian( G, false );
    SetIsSolvableGroup( G, false );
    SetRepresentative( G, -id );
    SetName( G, Concatenation( "RCWA(GF(", String(q), ")[",
                String(IndeterminatesOfPolynomialRing(R)[1]),"])" ) );
    return G;
  end );

#############################################################################
##
#F  RCWA( <R> ) . . . . . . . . . . . . . . . . . . . RCWA( <R> ) for PID <R>
##
InstallGlobalFunction( RCWA, R -> RCWACons( IsRcwaGroup, R ) );

#############################################################################
##
#M  IsNaturalRCWA_Z( <G> ) . . . . . . . . . . . . . . . . . . . . .  RCWA(Z)
##
##  The group RCWA(Z) can only be obtained by the above constructor.
##
InstallMethod( IsNaturalRCWA_Z,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               ReturnFalse );

#############################################################################
##
#M  IsNaturalRCWA_Z_pi( <G> ) . . . . . . . . . . . . . . . . . .  RCWA(Z_pi)
##
##  The groups RCWA($\Z_{(\pi)}$) can only be obtained by the above
##  constructor.
##
InstallMethod( IsNaturalRCWA_Z_pi,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               ReturnFalse );

#############################################################################
##
#M  IsNaturalRCWA_GF_q_x( <G> ) . . . . . . . . . . . . . . .  RCWA(GF(q)[x])
##
##  The groups RCWA(GF(q)[x]) can only be obtained by the above constructor.
##
InstallMethod( IsNaturalRCWA_GF_q_x,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               ReturnFalse );

#############################################################################
##
#M  IsSolvable( <G> ) . . . . . . . . . . . . . . . generic method for groups
##
InstallMethod( IsSolvable,
               "generic method for groups (RCWA)", true, [ IsGroup ],
               SUM_FLAGS,

  function ( G )
    if   HasIsSolvableGroup(G)
    then return IsSolvableGroup(G);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  IsPerfect( <G> ) . . . . . . . . . . . . . . .  generic method for groups
##
InstallMethod( IsPerfect,
               "generic method for groups (RCWA)", true, [ IsGroup ],
               SUM_FLAGS,

  function ( G )
    if   HasIsPerfectGroup(G)
    then return IsPerfectGroup(G);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  IsSimple( <G> ) . . . . . . . . . . . . . . . . generic method for groups
##
InstallMethod( IsSimple,
               "generic method for groups (RCWA)", true, [ IsGroup ],
               SUM_FLAGS,

  function ( G )
    if   HasIsSimpleGroup(G)
    then return IsSimpleGroup(G);
    else TryNextMethod(); fi;
  end );

# Auxiliary function for computing pairs of disjoint residue classes
# with modulus at most m.

ClassPairs := m -> Filtered(Cartesian([0..m-1],[1..m],[0..m-1],[1..m]),
                            t -> t[1] < t[2] and t[3] < t[4] and t[2] <= t[4]
                                 and (t[1]-t[3]) mod Gcd(t[2],t[4]) <> 0
                                 and (t[2] <> t[4] or t[1] < t[3]));
MakeReadOnlyGlobal( "ClassPairs" );

InstallValue( CLASS_PAIRS, [ 6, ClassPairs(6) ] );
InstallValue( CLASS_PAIRS_LARGE, CLASS_PAIRS );

#############################################################################
##
#M  Random( RCWA( Integers ) ) . . . . . . . . . .  random element of RCWA(Z)
##
InstallMethod( Random,
               "for RCWA(Z) (RCWA)", true, [ IsNaturalRCWA_Z ], 0,

  function ( RCWA_Z )

    local  Result, ClassTranspositions, ClassShifts, ClassReflections,
           GenFactors, Classes, tame, maxmodcscr, maxmodct, noct, nocs, nocr,
           deg, g, m, r, i;

    tame       := ValueOption("IsTame") = true;
    noct       := ValueOption("ClassTranspositions");
    nocs       := ValueOption("ClassShifts");
    nocr       := ValueOption("ClassReflections");
    maxmodcscr := ValueOption("ModulusBoundCSCR");
    maxmodct   := ValueOption("ModulusBoundCT");
    if noct   = fail then noct := Random([0..2]); fi;
    if nocs   = fail then nocs := Random([0..3]); fi;
    if nocr   = fail then nocr := Random([0..3]); fi;
    if maxmodcscr = fail then maxmodcscr :=  6; fi;
    if maxmodct   = fail then maxmodct   := 14; fi;
    if maxmodct <> CLASS_PAIRS_LARGE[1] then
      MakeReadWriteGlobal("CLASS_PAIRS_LARGE");
      CLASS_PAIRS_LARGE := [maxmodct,ClassPairs(maxmodct)];
      MakeReadOnlyGlobal("CLASS_PAIRS_LARGE");
    fi;
    Classes             := Combinations([1..maxmodcscr],2)-1;
    ClassTranspositions := List([1..noct],i->Random(CLASS_PAIRS[2]));
    if   Random([1..4]) = 1 
    then Add(ClassTranspositions,Random(CLASS_PAIRS_LARGE[2])); fi;
    ClassShifts         := List([1..nocs],i->Random(Classes));
    ClassReflections    := List([1..nocr],i->Random(Classes));
    ClassTranspositions := List(ClassTranspositions,ClassTransposition);
    ClassShifts         := List(ClassShifts,t->ClassShift(t)^Random([-1,1]));
    ClassReflections    := List(ClassReflections,ClassReflection);
    Result              :=   Product(ClassTranspositions)
                           * Product(ClassShifts)
                           * Product(ClassReflections);
    if Result = 1 then Result := One(RCWA_Z); fi;
    GenFactors := Concatenation(ClassTranspositions,ClassShifts,
                                ClassReflections);
    if not tame then SetFactorizationIntoGenerators(Result,GenFactors); fi;
    if tame then
      deg := Random([6,6,6,6,6,6,6,6,12,12,12,18]);
      g := Random(SymmetricGroup(deg));
      Result := RcwaMapping(g,[1..deg])^Result;
      SetIsTame(Result,true);
      SetOrder(Result,Order(g));
    fi;
    IsBijective(Result);
    return Result;
  end );

#############################################################################
##
#M  \in( <g>, RCWA( Integers ) ) . . .  for integral rcwa mapping and RCWA(Z)
##
InstallMethod( \in,
               "for integral rcwa mapping and RCWA(Z) (RCWA)", ReturnTrue,
               [ IsIntegralRcwaMapping, IsNaturalRCWA_Z ], 100,

  function ( g, G )
    return IsBijective(g);
  end );

#############################################################################
##
#M  \in( <g>, RCWA( Z_pi( <pi> ) ) ) . . . .  for rcwa mapping and RCWA(Z_pi)
##
InstallMethod( \in,
               "for semilocal integral rcwa mapping and RCWA(Z_pi) (RCWA)",
               ReturnTrue,
               [ IsSemilocalIntegralRcwaMapping, IsNaturalRCWA_Z_pi ], 100,

  function ( g, G )
    return FamilyObj(g) = FamilyObj(One(G)) and IsBijective(g);
  end );

#############################################################################
##
#M  \in( <g>, RCWA( GF(q)[x] ) ) . . . .  for rcwa mapping and RCWA(GF(q)[x])
##
InstallMethod( \in,
               "for modular rcwa mapping and RCWA(GF(q)[x]) (RCWA)",
               ReturnTrue, [ IsModularRcwaMapping, IsNaturalRCWA_GF_q_x ],
               100,

  function ( g, G )
    return FamilyObj(g) = FamilyObj(One(G)) and IsBijective(g);
  end );

#############################################################################
## 
#M  IsSubset( RCWA( Integers ), G ) . . . for RCWA(Z) and integral rcwa group
## 
InstallMethod( IsSubset,
               "for RCWA(Z) and integral rcwa group (RCWA)", ReturnTrue,
               [ IsNaturalRCWA_Z, IsIntegralRcwaGroup ], 0, ReturnTrue );

#############################################################################
##
#M  IsSubset( RCWA( Z_pi( <pi> ) ), G ) . . . . for RCWA(Z_pi) and rcwa group
##
InstallMethod( IsSubset,
               "for RCWA(Z_pi) and semilocal integral rcwa group (RCWA)",
               ReturnTrue,
               [ IsNaturalRCWA_Z_pi, IsSemilocalIntegralRcwaGroup ], 0,

  function ( RCWA_Z_pi, G )
    return FamilyObj(One(RCWA_Z_pi)) = FamilyObj(One(G));
  end );

#############################################################################
##
#M  IsSubset( RCWA( GF(q)[x] ), G ) . . . . for RCWA(GF(q)[x]) and rcwa group
##
InstallMethod( IsSubset,
               "for RCWA(GF(q)[x]) and modular rcwa group (RCWA)",
               ReturnTrue, [ IsNaturalRCWA_GF_q_x, IsModularRcwaGroup ], 0,

  function ( RCWA_GF_q_x, G )
    return FamilyObj(One(RCWA_GF_q_x)) = FamilyObj(One(G));
  end );

#############################################################################
##
#M  Display( RCWA( <R> ) ) . . . . . . . . . . . . . . . .  for whole RCWA(R)
##
InstallMethod( Display,
               "for whole RCWA(R) (RCWA)", true,
               [ IsRcwaGroup and HasName ], 0,

  function ( G )
    if   IsNaturalRCWA_Z( G ) or IsNaturalRCWA_Z_pi( G )
      or IsNaturalRCWA_GF_q_x( G )
    then Print( Name( G ), "\n" ); else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  ViewObj( <G> ) . . . . . . . . . . . . . . . . . . . . . . for rcwa group
##
InstallMethod( ViewObj,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  NrGens, RingString;

    RingString := RingToString(Source(One(G)));
    if   IsTrivial(G)
    then Display(G:NoLineFeed);
    else Print("<");
         if   HasIsTame(G) and not (HasSize(G) and IsInt(Size(G)))
         then if IsTame(G) then Print("tame "); else Print("wild "); fi; fi;
         NrGens := Length(GeneratorsOfGroup(G));
         Print("rcwa group over ",RingString," with ",NrGens," generator");
         if NrGens > 1 then Print("s"); fi;
         if not (HasIsTame(G) and not IsTame(G)) then
           if   HasIdGroup(G)
           then Print(", of isomorphism type ",IdGroup(G));
           elif HasSize(G)
           then Print(", of size ",Size(G)); fi;
         fi;
         Print(">");
    fi;
  end );

#############################################################################
##
#M  Display( <G> ) . . . . . . . . . . . . . . . . . . . . . . for rcwa group
##
InstallMethod( Display,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  RingString, g, prefix;

    RingString := RingToString(Source(One(G)));
    if   IsTrivial(G) 
    then Print("Trivial rcwa group over ",RingString);
         if ValueOption("NoLineFeed") <> true then Print("\n"); fi;
    else prefix := false;
         if HasIsTame(G) and not (HasSize(G) and IsInt(Size(G))) then
           if IsTame(G) then Print("\nTame "); else Print("\nWild "); fi;
           prefix := true;
         fi;
         if prefix then Print("rcwa "); else Print("\nRcwa "); fi;
         Print("group over ",RingString);
         if not (HasIsTame(G) and not IsTame(G)) then
           if   HasIdGroup(G) then Print(" of isomorphism type ",IdGroup(G));
           elif HasSize(G)    then Print(" of size ",Size(G)); fi;
         fi;
         Print(", generated by\n\n[\n");
         for g in GeneratorsOfGroup(G) do Display(g); od;
         Print("]\n\n");
    fi;
  end );

#############################################################################
##
#M  MovedPoints( <G> ) . . . . . . . . . . . . . . . . . . . . for rcwa group
##
##  The set of moved points (support) of the rcwa group <G>.
##
InstallOtherMethod( MovedPoints,
                    "for rcwa group (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    if IsNaturalRCWA_Z(G) or IsNaturalRCWA_Z_pi(G) or IsNaturalRCWA_GF_q_x(G)
    then return Source(One(G)); fi;
    return Union(List(GeneratorsOfGroup(G),MovedPoints));
  end );

#############################################################################
##
#M  IsomorphismIntegralRcwaGroup( <G> ) . . . . .  rcwa representation of <G>
#M  IsomorphismRcwaGroup( <G> )
##
##  This is a rather simple-minded method.
##
InstallMethod( IsomorphismIntegralRcwaGroup,
               "generic method for finite groups (RCWA)", true,
               [ IsGroup and IsFinite ], 0,

  function ( G )

    local  G2, H, phi1, phi2, n;

    if IsIntegralRcwaGroup(G) then return IdentityMapping(G); fi;
    if   not IsPermGroup(G) 
    then phi1 := IsomorphismPermGroup(G); G2 := Image(phi1);
    else phi1 := IdentityMapping(G);      G2 := G;
    fi;
    n := LargestMovedPoint(G2);
    H := GroupWithGenerators(List(GeneratorsOfGroup(G2),
                                  g -> RcwaMapping(g,[1..n])));
    phi2 := GroupHomomorphismByImagesNC(G2,H,GeneratorsOfGroup(G2),
                                             GeneratorsOfGroup(H));
    return Immutable(CompositionMapping(phi2,phi1));
  end );

#############################################################################
##
#F  IntegralRcwaGroupByPermGroup( <G> ) . . . .  rcwa group isomorphic to <G>
#F  RcwaGroupByPermGroup( <G> )
##
InstallGlobalFunction( IntegralRcwaGroupByPermGroup,

  function ( G )

    local  H, phi, phi_1;

    if   not IsPermGroup(G) 
    then Error("<G> must be a permutation group"); fi;
    phi := IsomorphismIntegralRcwaGroup(G);
    H   := Image(phi);
    phi_1 := InverseGeneralMapping(phi);
    SetIsomorphismPermGroup(H,phi_1);
    SetNiceMonomorphism(H,phi_1);
    SetNiceObject(H,G);
    # SetIsHandledByNiceMonomorphism(H,true);

    return H;
  end );

#############################################################################
##
#M  PrimeSet( <G> ) . . . . . . . . . . . . . . . . . . . . .  for rcwa group
##
InstallMethod( PrimeSet,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> Union( List( GeneratorsOfGroup( G ), PrimeSet ) ) );

#############################################################################
##
#M  IsIntegral( <G> ) . . . . . . . . . . . . . . . . . . . .  for rcwa group
##
InstallOtherMethod( IsIntegral,
                    "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0, 
                    G -> ForAll( GeneratorsOfGroup( G ), IsIntegral ) );

#############################################################################
##
#M  IsClassWiseOrderPreserving( <G> ) . . . . . for rational-based rcwa group
##
##  We say that a rational-based rcwa group is *class-wise order-preserving*
##  if all of its elements are.
##
InstallOtherMethod( IsClassWiseOrderPreserving,
                    "for rational-based rcwa groups (RCWA)",
                    true, [ IsRationalBasedRcwaGroup ], 0,
                    G -> ForAll( GeneratorsOfGroup( G ),
                                 IsClassWiseOrderPreserving ) );

#############################################################################
## 
#M  ShortOrbits( <G>, <S>, <maxlng> ) . . . . . . . . . . . .  for rcwa group
## 
InstallMethod( ShortOrbits,
               "for rcwa groups (RCWA)", true,
               [ IsRcwaGroup, IsList, IsPosInt ], 0,

  function ( G, S, maxlng )

    local  gens, g, orbs, orb, oldorb, remaining, n;

    gens := GeneratorsOfGroup(G);
    orbs := []; remaining := ShallowCopy(Set(S));
    while remaining <> [] do
      orb := [remaining[1]];
      repeat
        oldorb := ShallowCopy(orb);
        for g in gens do for n in oldorb do AddSet(orb,n^g); od; od;
      until Length(orb) > maxlng or Length(orb) = Length(oldorb);
      if Length(orb) <= maxlng then Add(orbs,Set(orb)); fi;
      remaining := Difference(remaining,orb);
    od;
    return orbs;
  end );

#############################################################################
##
#M  OrbitsModulo( <G>, <m> ) . . . . . . . . .  for rational-based rcwa group
##
InstallOtherMethod( OrbitsModulo,
                    "for rational-based rcwa groups (RCWA)", true,
                    [ IsRationalBasedRcwaGroup, IsPosInt ], 0,

  function ( G, m )

    local  result, orbsgen, orbit, oldorbit, remaining;

    orbsgen := Concatenation(List(GeneratorsOfGroup(G),
                                  g->OrbitsModulo(g,m)));
    remaining := [0..m-1]; result := [];
    repeat
      orbit := [remaining[1]];
      repeat
        oldorbit := ShallowCopy(orbit);
        orbit := Union(orbit,
                       Union(Filtered(orbsgen,
                                      orb->Intersection(orbit,orb)<>[])));
      until orbit = oldorbit;
      Add(result,orbit);
      remaining := Difference(remaining,orbit);
    until remaining = [];
    return result;
  end );

CheckModulus := function ( G, m )

  local  IsAffine, R, P, gens, errormessage;

  IsAffine := function ( g, cl )

    local  m, c, res, cls;

    m := Modulus(g); c := Coefficients(g); res := AllResidues(R,m);
    cls := Filtered(List(res,r->ResidueClass(R,m,r)),
                    clm->Intersection(clm,cl)<>[]);
    return Length(Set(c{List(cls,clm->Position(res,Residues(clm)[1]))})) = 1;
  end;

  Info(InfoRCWA,2,"Checking modulus ...");
  errormessage := Concatenation(
                  "the modulus computation failed --\n",
                  "please send the generators of the group you tested ",
                  "to Stefan Kohl, kohl@mathematik.uni-stuttgart.de.\n");
  R := Source(One(G)); P := RespectedPartition(G);
  if   not IsZero(Lcm(List(P,Modulus)) mod m)
    or not IsGroup(ActionOnRespectedPartition(G))
  then Error(errormessage); fi;
  gens := GeneratorsOfGroup(G);
  if   not ForAll(gens,g->ForAll(P,cl->IsAffine(g,cl)))
  then Error(errormessage); fi;
end;
MakeReadOnlyGlobal( "CheckModulus" );

#############################################################################
##
#M  Modulus( <G> ) . . . . . . . . . . . . . . . . . . . . . . for rcwa group
##
##  Modulus of rcwa group <G>.
##
##  We define the modulus of an rcwa group <G> by the least common multiple
##  of the moduli of its elements.
##
InstallMethod( Modulus,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  R, m, oldmod, maxfinmod, g, gens, els, step, maxstep;

    if HasModulusOfRcwaGroup(G) then return ModulusOfRcwaGroup(G); fi;
    R := Source(One(G)); gens := GeneratorsOfGroup(G);
    if IsIntegral(G) then
      Info(InfoRCWA,3,"Modulus: <G> is integral.");
      m := Lcm(R,List(gens,Modulus));
      SetModulusOfRcwaGroup(G,m); return m;
    fi;
    if not ForAll(gens,IsTame) then
      Info(InfoRCWA,3,"Modulus: <G> has a wild generator.");
      SetModulusOfRcwaGroup(G,Zero(R)); return Zero(R);
    fi;
    if Length(gens) = 1 then
      Info(InfoRCWA,3,"Modulus: <G> is cyclic and the generator is tame.");
      m := Lcm(R,Modulus(gens[1]),   Modulus(gens[1]^-1),
                 Modulus(gens[1]^17),Modulus(gens[1]^97)); # probabilistic.
      SetModulusOfRcwaGroup(G,m); CheckModulus(G,m); return m;
    fi;
    els := Union(gens,List(Tuples(gens,2),t->t[1]*t[2]),
                      List(Tuples(gens,2),t->Comm(t[1],t[2])));
    if not ForAll(els,IsTame) then
      Info(InfoRCWA,3,"Modulus: <G> has a wild 2-generator product ",
                      "or 2-generator commutator.");
      SetModulusOfRcwaGroup(G,Zero(R)); return Zero(R);
    fi;
    m := Lcm(R,List(els,Modulus));
    Info(InfoRCWA,1,"Trying probabilistic random walk, initial m = ",m);
    maxfinmod := Lcm(R,List(gens,Divisor)) * m;
    step := 1; maxstep := 10 * Length(gens); g := gens[1];
    repeat # probabilistic.
      g := g * Random(gens); step := step + 1;
      if not IsZero(m mod Modulus(g)) then
        m := Lcm(m,Modulus(g)); step := 1;
      fi;
      if   Length(AllResidues(R,m)) > Length(AllResidues(R,maxfinmod))
      then TryNextMethod(); fi; # Here the modulus is likely 0.
    until step > maxstep;
    SetModulusOfRcwaGroup(G,m);
    CheckModulus(G,m); # Verification of probabilistic result.
    return m;
  end );

#############################################################################
##
#M  ModulusOfRcwaGroup( <G> ) . . . . . . . . . . . . . . . .  for rcwa group
##
InstallMethod( ModulusOfRcwaGroup,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> Modulus( G ) );

#############################################################################
##
#M  IsTame( <G> ) . . . . . . . . . . . . . . . . . . . . . .  for rcwa group
##
InstallMethod( IsTame,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> Modulus( G ) <> Zero( Source( One( G ) ) ) );

#############################################################################
##
#M  RespectedPartition( <G> ) . . . . . . . . . . . . . . for tame rcwa group
##
InstallOtherMethod( RespectedPartition,
                    "for tame rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  R, m, moved, fixed, pcp, untouched, cls, cl, orb, r, i;

    if not IsTame(G) then return fail; fi;
    R := Source(One(G)); m := Modulus(G); moved := MovedPoints(G);
    if   IsUnionOfResidueClasses(moved) and Modulus(moved) <> One(R)
    then fixed := Residues(Difference(R,moved));
    elif moved <> [] then fixed := []; else fixed := [0]; fi;
    pcp := List(fixed,i->ResidueClass(R,m,i));
    untouched := Difference(AllResidues(R,m),fixed);
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
#M  ActionOnRespectedPartition( <G> ) . . . . . . . . . . for tame rcwa group
##
InstallMethod( ActionOnRespectedPartition,
               "for tame rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> Action( G, RespectedPartition( G ) ) );

#############################################################################
##
#M  RankOfKernelOfActionOnRespectedPartition( <G> )  for tame rcwa gp. over Z
##
InstallMethod( RankOfKernelOfActionOnRespectedPartition,
               "for tame integral rcwa groups (RCWA)", true,
               [ IsIntegralRcwaGroup ], 0,
               G -> Length( KernelOfActionOnRespectedPartitionHNFMat(G) ) );

#############################################################################
##
#M  KernelOfActionOnRespectedPartition( <G> ) .  for tame integral rcwa group
##
##  This is a probabilistic method, i.e. it may return a proper subgroup of
##  the actual kernel. In particular, it is not taken care of torsion
##  elements in the kernel, which can occur is <G> is not class-wise order-
##  preserving.
##  
InstallMethod( KernelOfActionOnRespectedPartition,
               "for cwop. tame integral rcwa groups (RCWA)", true,
               [ IsIntegralRcwaGroup ], 0,

  function ( G )

    local  P, K, H, M, L, l, LHNF, T, lng, ModG, g, h, nrgens,
           genK, genKHNF, elH, elG, elK, c, nr, lasthit, erg, i;

    if ValueOption("ProperSubgroupAllowed") <> true then
      if not IsClassWiseOrderPreserving(G) then TryNextMethod(); fi;
      Info(InfoWarning,1,"Warning: `KernelOfActionOnRespectedPartition' ",
                         "is probabilistic.");
    fi;

    ModG := Modulus(G);
    P := RespectedPartition(G);
    H := ActionOnRespectedPartition(G);
    g := GeneratorsOfGroup(G); h := GeneratorsOfGroup(H);
    nrgens := Length(g); elH := h[1]; elG := g[1]; L := [];
    lng := 0; nr := 1; lasthit := 1; genK := [];
    repeat
      elK := elG^Order(elH);
      c   := Coefficients(elK);
      l   := List([1..Length(P)],
                  i -> c[Residues(P[i])[1] mod Modulus(elK) + 1][2]);
      if SolutionIntMat(L,l) = fail or (L = [] and not ForAll(l,IsZero)) then
        lng := lng + 1; Add(L,l); Add(genK,elK); lasthit := nr;
        Info(InfoRCWA,3,"KernelOfActionOnRespectedPartition: gen. #",nr,
                        ", lng = ",lng);
      fi;
      i := Random([1..nrgens]); nr := nr + 1;
      elH := elH * h[i];
      elG := elG * g[i];
    until nr - lasthit > lasthit + 100; # This is probabilistic. 
    erg := HermiteNormalFormIntegerMatTransforms(L{[1..lng]});
    LHNF := erg.normal; T := erg.rowtrans;
    genKHNF := List([1..lng],
                    i->Product(List([1..lng],j->genK[j]^T[i][j])));
    LHNF := Filtered(LHNF,l->not IsZero(l));
    genKHNF := Filtered(genKHNF,k->not IsOne(k));
    SetKernelOfActionOnRespectedPartitionHNFMat(G,LHNF);
    if genKHNF <> [] then K := Group(genKHNF);
                     else K := TrivialSubgroup(G); fi;
    SetRespectedPartition(K,P);
    SetKernelOfActionOnRespectedPartition(K,K);
    SetRankOfKernelOfActionOnRespectedPartition(K,Length(genKHNF));
    SetKernelOfActionOnRespectedPartitionHNFMat(K,LHNF);
    return K;
  end );

#############################################################################
##
#M  KernelOfActionOnRespectedPartitionHNFMat( <G> )  for tame rcwa gp. over Z
##
InstallMethod( KernelOfActionOnRespectedPartitionHNFMat,
               "for tame integral rcwa groups (RCWA)", true,
               [ IsIntegralRcwaGroup ], 0,

  function ( G )
    KernelOfActionOnRespectedPartition(G);
    return KernelOfActionOnRespectedPartitionHNFMat(G);
  end );

#############################################################################
##
#M  IsomorphismPermGroup( <G> ) . . . . . . . . . . . . for finite rcwa group
##
InstallMethod( IsomorphismPermGroup,
               "for finite rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  phi, H, orb, S, S_old, g;

    if ForAny(GeneratorsOfGroup(G),g->Order(g)=infinity) or not IsTame(G)
    or RankOfKernelOfActionOnRespectedPartition(G:ProperSubgroupAllowed) > 0
    then return fail; fi;

    # Note that a class reflection of a residue class r(m) can fix
    # one element in r(m), but not two. This means that <G> acts
    # faithfully on the orbit containing the following set <S>:

    if   IsClassWiseOrderPreserving(G)
    then S := List(RespectedPartition(G),Representative);
    else S := Flat(List(RespectedPartition(G),
                        cl->[0,Modulus(cl)]+Representative(cl)));
    fi;

    repeat
      S_old := ShallowCopy(S);
      for g in GeneratorsOfGroup(G) do S := Union(S,S^g); od;
      if   Length(S) > 10 * Length(RespectedPartition(G))
      then TryNextMethod(); fi;
    until S = S_old;
    H   := Action(G,S); # Now, <G> must act faithfully on <S>.
    orb := First(Orbits(H,MovedPoints(H)),M->Size(Action(H,M))=Size(H));
    if orb <> fail then
      H := GroupWithGenerators(List(GeneratorsOfGroup(H),
                                    h->Permutation(h,orb)));
    fi;
    phi := Immutable(EpimorphismByGeneratorsNC(G,H));
    if   not HasParent(G)
    then SetNiceMonomorphism(G,phi); SetNiceObject(G,H); fi;

    return phi;
  end );

#############################################################################
##
#M  IsomorphismMatrixGroup( <G> ) . . . . . . . . . . . . for tame rcwa group
##
InstallMethod( IsomorphismMatrixGroup,
               "for tame rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  R, res, q, x, d, P, H, M, ModG, g, h, m, deg, r, b, c, pos, i, j;

    if not IsTame(G) then TryNextMethod(); fi;
    R := Source(One(G)); ModG := Modulus(G);
    if IsModularRcwaGroup(G) then
      q := Size(CoefficientsRing(R));
      x := IndeterminatesOfPolynomialRing(R)[1];
      res := [];
      for d in [1..DegreeOfLaurentPolynomial(ModG)] do
        res[d] := AllGFqPolynomialsModDegree(q,d,x);
      od;
    fi;
    g := GeneratorsOfGroup(G);
    P := RespectedPartition(G);
    deg := 2 * Length(P);
    H := Action(G,P); h := GeneratorsOfGroup(H);
    m := [];
    for i in [1..Length(g)] do
      m[i] := MutableNullMat(deg,deg,R);
      for j in [1..deg/2] do
        b := [[0,0],[0,1]] * One(R);
        r := Residues(P[j])[1] mod Modulus(g[i]);
        if   IsRationalBasedRcwaGroup(G)
        then pos := r+1;
        else pos := Position(res[DegreeOfLaurentPolynomial(g[i])],r); fi;
        c := Coefficients(g[i])[pos];
        b[1] := [c[1]/c[3],c[2]/c[3]];
        m[i]{[2*j^h[i]-1..2*j^h[i]]}{[2*j-1..2*j]} := b;
      od;
    od;
    M := Group(m);
    return GroupHomomorphismByImagesNC(G,M,g,m);
  end );

#############################################################################
##
#M  NiceMonomorphism( <G> ) . . . . . . . . . . . . . . . for tame rcwa group
##
InstallMethod( NiceMonomorphism,
               "for tame rcwa groups (RCWA)", true,
               [ IsIntegralRcwaGroup ], 0,

  function ( G )

    if   IsTame(G)
    then if   IsTrivial(KernelOfActionOnRespectedPartition(G))
         then return IsomorphismPermGroup(G);
         else return IsomorphismMatrixGroup(G); fi;
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  NiceObject( <G> ) . . . . . . . . . . . . . . . . . . . .  for rcwa group
##
InstallMethod( NiceObject,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> Image( NiceMonomorphism( G ) ) );

#############################################################################
##
#M  \in( <g>, <G> ) . . . . for integral rcwa mapping and integral rcwa group
##
##  If <G> is wild this may run into an infinite loop if <g> is not an
##  element of <G>.
##
InstallMethod( \in,
               "for integral rcwa mapping and integral rcwa group (RCWA)",
               ReturnTrue, [ IsIntegralRcwaMapping, IsIntegralRcwaGroup ], 0,

  function ( g, G )

    local  P, H, h, K, k, L, l, F, phi, c, gens, gensinv;

    Info(InfoRCWA,2,"\\in for an rcwa mapping of Z ",
                    "and an rcwa group over Z");
    if not IsBijective(g)
    then Info(InfoRCWA,4,"<g> is not bijective."); return false; fi;
    gens := GeneratorsOfGroup(G);
    if IsOne(g) or g in gens or g^-1 in gens then
      Info(InfoRCWA,4,"<g> = 1 or one of <g> or <g>^-1 ",
                      "in generator list of <G>.");
      return true;
    fi;
    if not IsSubset(PrimeSet(G),PrimeSet(g)) then
      Info(InfoRCWA,4,"<g> and <G> have incompatible prime sets.");
      return false;
    fi;
    if        IsClassWiseOrderPreserving(G)
      and not IsClassWiseOrderPreserving(g) then
      Info(InfoRCWA,4,"<G> is class-wise order-preserving, <g> is not.");
      return false;
    fi;
    if not IsSubset(MovedPoints(G),MovedPoints(g)) then
      Info(InfoRCWA,4,"supp(<g>) is not a subset of supp(<G>).");
      return false;
    fi;
    if not IsTame(G) then
      Info(InfoRCWA,3,"<G> is wild -- trying to factor <g> into gen's ...");
      phi := EpimorphismFromFreeGroup(G);
      return PreImagesRepresentative(phi,g) <> fail;
    else
      if Modulus(G) mod Modulus(g) <> 0 then
        Info(InfoRCWA,4,"Mod(<g>) does not divide Mod(<G>).");
        return false;
      fi;
      if IsFinite(G) and Order(g) = infinity then
        Info(InfoRCWA,3,"<G> is finite, but <g> has infinite order.");
        return false;
      fi;
      if not IsTame(g) then
        Info(InfoRCWA,3,"<G> is tame, but <g> is wild.");
        return false;
      fi;
      P := RespectedPartition(G);
      H := ActionOnRespectedPartition(G);
      h := Permutation(g,P);
      if h = fail then
        Info(InfoRCWA,3,"<g> does not act on RespectedPartition(<G>).");
        return false;
      fi;
      if not h in H then
        Info(InfoRCWA,3,"The action of <g> on RespectedPartition(<G>) ",
                        "is not an element of the one of <G>.");
        return false;
      fi;

      # The following uses the operation `KernelOfActionOnClassPartition',
      # for which currently only a probabilistic method is available.
      # The group returned by this function can be a proper subgroup
      # of the actual kernel. Thus, membership can only be decided to the
      # positive here.

      if IsClassWiseOrderPreserving(G) then
        Info(InfoRCWA,3,"Compute an element of <G> which acts like <g>");
        Info(InfoRCWA,3,"on RespectedPartition(<G>).");
        phi := EpimorphismFromFreeGroup(H);
        h   := PreImagesRepresentative(phi,h:NoStabChain);
        if h = fail then return false; fi;
        h   := Product(List(LetterRepAssocWord(h),
                            id->gens[AbsInt(id)]^SignInt(id)));
        k   := g/h;
        Info(InfoRCWA,3,"Check membership of the quotient in the kernel of");
        Info(InfoRCWA,3,"the action of <g> on RespectedPartition(<G>).");
        K:=KernelOfActionOnRespectedPartition(G:ProperSubgroupAllowed);
        L:=KernelOfActionOnRespectedPartitionHNFMat(G:ProperSubgroupAllowed);
        if L = [] then return IsOne(k); fi;
        Info(InfoRCWA,3,"The kernel has rank ",Length(L),".");
        c := Coefficients(k);
        l := List(P,cl->c[Residues(cl)[1] mod Modulus(k) + 1][2]);
        if SolutionIntMat(L,l) <> fail then return true; fi;
      fi;

      # Finally, a brute force factorization attempt:

      Info(InfoRCWA,3,"Trying to factor <g> into gen's ...");
      phi := EpimorphismFromFreeGroup(G);
      return PreImagesRepresentative(phi,g) <> fail;
    fi;
  end );

#############################################################################
##
#M  \in( <g>, <G> ) . . . . . . . . . . . . . for rcwa mapping and rcwa group
##
##  This may run into an infinite loop if <G> is infinite and <g> is not an
##  element of <G>.
##
InstallMethod( \in,
               "for rcwa mapping and rcwa group (RCWA)",
               ReturnTrue, [ IsRcwaMapping, IsRcwaGroup ], 0,

  function ( g, G )

    local  gens, k;

    if FamilyObj(g) <> FamilyObj(One(G)) then return false; fi;
    gens := GeneratorsOfGroup(G);
    if IsOne(g) or g in gens or g^-1 in gens then return true; fi;
    if not IsSubset(PrimeSet(G),PrimeSet(g)) then return false; fi;
    if   g in List(Combinations(gens,2), t -> Product(t))
    then return true; fi;
    gens := Union(gens,List(gens, g -> g^-1));
    k := 2;
    repeat
      if   g in List(Tuples(gens,k), t -> Product(t))
      then return true; fi;
      k := k + 1;
    until false;
  end );

#############################################################################
##
#M  Size( <G> ) . . . . . . . . . . . . . . . . . . . for integral rcwa group
##
##  This method checks whether <G> is tame and the kernel of the action of
##  <G> on a respected partition has rank 0 -- if so, it returns the
##  size of the permutation group induced on this partition, and if not it
##  returns infinity.
##
InstallMethod( Size,
               "for rcwa groups, use action on respected partition (RCWA)",
               true, [ IsIntegralRcwaGroup ], 0,

  function ( G )

    local  S, S_old, g;

    # A few `trivial' checks.

    if IsTrivial(G) then return 1; fi;
    if ForAny(GeneratorsOfGroup(G),g->Order(g)=infinity)
    then return infinity; fi;
    if not IsTame(G) then return infinity; fi;

    # Look for an infinite cyclic subgroup in the kernel of the action
    # of <G> on a respected partition.

    Info(InfoRCWA,1,"Size: use action on respected partition.");
    if RankOfKernelOfActionOnRespectedPartition(G:ProperSubgroupAllowed) > 0
    then return infinity; fi;

    # If we have not found one, the group <G> is likely finite.

    # Note that a class reflection of a residue class r(m) can fix
    # one element in r(m), but not two. This means that <G> acts
    # faithfully on the orbit containing the following set <S>:

    if   IsClassWiseOrderPreserving(G)
    then S := List(RespectedPartition(G),Representative);
    else S := Flat(List(RespectedPartition(G),
                        cl->[0,Modulus(cl)]+Representative(cl)));
    fi;

    repeat
      S_old := ShallowCopy(S);
      for g in GeneratorsOfGroup(G) do S := Union(S,S^g); od;
      if   Length(S) > 10 * Length(RespectedPartition(G))
      then TryNextMethod(); fi;
    until S = S_old;

    return Size(Action(G,S)); # Now, <G> must act faithfully on <S>.
  end );

#############################################################################
##
#M  Size( <G> ) . . . . . . . . . . . . . . . . . . . . . . .  for rcwa group
##
##  This method looks for elements of infinite order.
##  In case this search is not successful, it gives up.
##
InstallMethod( Size,
               "for rcwa groups, look for elements of infinite order (RCWA)",
               true, [ IsRcwaGroup ], 0,

  function ( G )

    local  gen, k;

    Info(InfoRCWA,1,"Size: look for elements of infinite order.");
    gen := GeneratorsOfGroup(G);
    if ForAny(gen, g -> Order(g) = infinity) then return infinity; fi;
    if   ForAny(Combinations(gen,2), t -> Order(Comm(t[1],t[2])) = infinity)
    then return infinity; fi;
    for k in [2..3] do
      if   ForAny(Tuples(gen,k), t -> Order(Product(t)) = infinity)
      then return infinity; fi;
    od;
    TryNextMethod();
  end );

#############################################################################
##
#M  IntegralizingConjugator( <sigma> ) .  for tame bij. integral rcwa mapping
##
InstallMethod( IntegralizingConjugator,
               "for tame bijective integral rcwa mappings (RCWA)", true,
               [ IsIntegralRcwaMapping ], 0,

  function ( sigma )

    local  pcp, c, m, mtilde, r, rtilde, cl, m_cl, i, j;

    if IsIntegral(sigma) then return One(sigma); fi;
    pcp := RespectedPartition(sigma); 
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
#M  IntegralConjugate( <f> ) . . . . . . . . . . . . .  for tame rcwa mapping
##
InstallMethod( IntegralConjugate,
               "for tame rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               f -> f^IntegralizingConjugator( f ) );

#############################################################################
##
#M  IntegralizingConjugator( <G> ) . . . . . . . for tame integral rcwa group
##
InstallOtherMethod( IntegralizingConjugator,
                    "for tame integral rcwa groups (RCWA)", true,
                    [ IsIntegralRcwaGroup ], 0,

  function ( G )

    local  pcp, c, m, mtilde, r, rtilde, cl, m_cl, i, j;

    if IsIntegral(G) then return One(G); fi;
    pcp := RespectedPartition(G); 
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
#M  IntegralConjugate( <G> ) . . . . . . . . . . . . . .  for tame rcwa group
##
InstallOtherMethod( IntegralConjugate,
                    "for tame rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
                    G -> G^IntegralizingConjugator( G ) );

#############################################################################
##
#M  StandardizingConjugator( <sigma> ) .  for tame bij. integral rcwa mapping
##
InstallMethod( StandardizingConjugator,
               "for tame bijective integral rcwa mappings (RCWA)", true,
               [ IsIntegralRcwaMapping ], 0,

  function ( sigma )

    local  toflat, flat, m, mtilde, mTilde, r, rtilde, c, pcp, cycs, lngs,
           cohorts, cohort, l, nrcycs, res, cyc, n, ntilde, i, j, k;

    if not (IsBijective(sigma) and IsTame(sigma)) then return fail; fi;
    if not IsIntegral(sigma) then
      toflat := IntegralizingConjugator(sigma);
      flat   := sigma^toflat;
    else toflat := One(sigma); flat := sigma; fi;
    m := Modulus(flat); pcp := RespectedPartition(flat);
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
               "for tame rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               f -> f^StandardizingConjugator( f ) );

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
                    "for two integral rcwa mappings, in RCWA(Z) (RCWA)",
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
##  `RCWA( Z_pi( <pi> ) )'. Only trivial checks are done.
##  The method cannot find a positive result unless <f> and <g> are equal.
##
InstallOtherMethod( IsConjugate,
                    Concatenation("for two semilocal integral rcwa ",
                                  "mappings in RCWA(Z_pi) (RCWA)"),
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
#M  RepresentativeActionOp( RCWA( Integers ), <f>, <g>, <act> ) 
##
##  For tame integral rcwa mappings under the conjugation action in the full
##  group `RCWA( Integers )'. The method returns an rcwa mapping <h> such
##  that <f>^<h> = <g>, in case such a mapping exists and fail otherwise.
##  The action <act> must be `OnPoints'.
##
InstallOtherMethod( RepresentativeActionOp,
                    "for RCWA(Z) and two tame integral rcwa mappings (RCWA)",
                    true,
                    [ IsNaturalRCWA_Z, 
                      IsIntegralRcwaMapping, IsIntegralRcwaMapping,
                      IsFunction ], 0,

  function ( RCWA_Z, f, g, act )

    if act <> OnPoints then TryNextMethod(); fi;
    if f = g then return One(f); fi;
    if not ForAll([f,g],IsTame) then TryNextMethod(); fi;
    if Order(f) <> Order(g) then return fail; fi;
    if StandardConjugate(f) <> StandardConjugate(g) then return fail; fi;
    return StandardizingConjugator(f) * StandardizingConjugator(g)^-1;
  end );

#############################################################################
##
#M  RepresentativeActionOp( RCWA( Integers ), <S1>, <S2>, <act> ) 
##
##  An rcwa mapping <g> which maps <S1> to <S2>.
##  The sets <S1> and <S2> have to be unions of residue classes of $\Z$.
##  The argument <act> is ignored.
##
InstallOtherMethod( RepresentativeActionOp,
                    "for RCWA(Z) and two residue class unions (RCWA)", true,
                    [ IsNaturalRCWA_Z, IsUnionOfResidueClassesOfZ,
                      IsUnionOfResidueClassesOfZ, IsFunction ], 0,

  function ( RCWA_Z, S1, S2, act )

    local  Refine, Refinement, S, C, g;

    Refinement := function ( cls, lng )

      local  m, M, k, splitcl, parts;

      while Length(cls) <> lng do
        m       := Minimum(List(cls,Modulus));
        M       := Lcm(List(cls,Modulus));
        splitcl := First(cls,cl->Modulus(cl)=m); RemoveSet(cls,splitcl);
        k       := Maximum(Filtered(DivisorsInt(M/m),d->d<=lng-Length(cls)));
        if k = 1 then k := 2; fi;
        parts   := SplittedClass(splitcl,k);
        cls     := Union(cls,parts);
      od;
      return cls;
    end;

    Refine := function ( S )
      if   Length(S[1]) > Length(S[2])
      then S[2] := Refinement(S[2],Length(S[1]));
      elif Length(S[2]) > Length(S[1])
      then S[1] := Refinement(S[1],Length(S[2])); fi;
    end;

    S := List([S1,S2],AsUnionOfFewClasses);
    C := List([S1,S2],Si->AsUnionOfFewClasses(Difference(Integers,Si)));
    Refine(S); Refine(C);
    g := RcwaMapping(Concatenation(S[1],C[1]),Concatenation(S[2],C[2]));
    return g;
  end );

#############################################################################
##
#M  RepresentativeActionOp( RCWA( Integers ), <P1>, <P2>, <act> ) 
##
##  An rcwa mapping <g> which maps <P1> to <P2> and is
##
##  - affine on the elements of <P1>, if the option `IsTame' is not set,
##  - tame, if the option `IsTame' is set.
##
##  The arguments <P1> and <P2> must be partitions of $\Z$ into equally many
##  disjoint residue classes, and the argument <act> is ignored.
##
InstallOtherMethod( RepresentativeActionOp,
                    "for RCWA(Z) and two class partitions (RCWA)", true,
                    [ IsNaturalRCWA_Z, IsList, IsList, IsFunction ], 0,

  function ( RCWA_Z, P1, P2, act )

    local  SplitClass, g, tame, m, c, P, Phat, Buckets, b,
           k, ri, mi, rtildei, mtildei, ar, br, cr, r, i, j;

    SplitClass := function ( i, j )

      local  mods, pos, m, r, mtilde, r1, r2, j2, pos2;

      mods := List(Buckets[i][j],Modulus);
      m    := Minimum(mods);
      pos  := Position(mods,m);
      r    := Residues(Buckets[i][j][pos])[1];
      mtilde := 2*m; r1 := r; r2 := r + m;
      Buckets[i][j] := Union(Difference(Buckets[i][j],[Buckets[i][j][pos]]),
                             [ResidueClass(Integers,mtilde,r1),
                              ResidueClass(Integers,mtilde,r2)]);
      j2  := Filtered([1..k],
                      j->Position(Buckets[3-i][j],
                                  ResidueClass(Integers,m,r))<>fail)[1];
      pos2 := Position(Buckets[3-i][j2],ResidueClass(Integers,m,r));
      Buckets[3-i][j2] := Union(Difference( Buckets[3-i][j2],
                                           [Buckets[3-i][j2][pos2]]),
                                [ResidueClass(Integers,mtilde,r1),
                                 ResidueClass(Integers,mtilde,r2)]);
    end;

    g := RcwaMapping(P1,P2); # Do this always. If tame, just to check arg's.

    if ValueOption("IsTame") = true then
      k       := Length(P1);
      m       := Lcm(List(Union(P1,P2),Modulus));
      P       := [P1,P2];
      Phat    := List([0..m-1],r->ResidueClass(Integers,m,r));
      Buckets := List([1..2],i->List([1..k],j->Filtered(Phat,
                 cl->Residues(cl)[1] mod Modulus(P[i][j]) =
                 Residues(P[i][j])[1])));
      repeat
        for i in [1..k] do
          b := [Buckets[1][i],Buckets[2][i]];
          if Length(b[2]) > Length(b[1]) then
            for j in [1..Length(b[2])-Length(b[1])] do
              SplitClass(1,i);
            od;
          elif Length(b[1]) > Length(b[2]) then
            for j in [1..Length(b[1])-Length(b[2])] do
              SplitClass(2,i);
            od;
          fi;
        od;
      until ForAll([1..k],i->Length(Buckets[1][i]) = Length(Buckets[2][i]));
      g := RcwaMapping(Flat(Buckets[1]),Flat(Buckets[2]));
      SetIsTame(g,true); SetRespectedPartition(g,Set(Flat(Buckets[1])));
    fi;
    return g;
  end );

#############################################################################
## 
#M  OrbitUnion( <G>, <S> ) . . . . . . . . . . . . . . for rcwa group and set
##
##  This method might run into an infinite loop.
## 
InstallMethod( OrbitUnion,
               "for rcwa group and set (RCWA)", ReturnTrue,
               [ IsRcwaGroup, IsListOrCollection ], 0,

  function ( G, S )

    local  R, gen, image, oldimage, g;

    Info(InfoRCWA,1,"OrbitUnion: initial set = ",S);
    R := Source(One(G));
    gen := GeneratorsOfGroup(G); gen := Union(gen,List(gen,g->g^-1));
    image := S;
    repeat
      oldimage := image;
      for g in gen do image := Union(image,ImagesSet(g,image)); od;
      Info(InfoRCWA,2,"Image = ",image);
    until image = R or image = oldimage;
    return image;
  end );

#############################################################################
##
#M  IsTransitive( <G>, <S> ) . . . . . for rcwa group and residue class union
##
##  This method might fail or run into an infinite loop.
##
InstallOtherMethod( IsTransitive,
                    "for rcwa group and residue class union (RCWA)",
                    ReturnTrue, [ IsRcwaGroup, IsListOrCollection ],
                    0,

  function ( G, S )

    local  ShortOrbitsFound, ShiftedClass, ShiftedClassPowers,
           R, x, gen, comm, el, WordLng, cl, ranges, range;

    ShortOrbitsFound := function ( range, maxlng )
      
      local  orb;

      orb := ShortOrbits(G,range,maxlng);
      if orb <> [] then
        Info(InfoRCWA,1,"The group has the finite orbits ",orb);
        return true;
      else return false; fi;
    end;

    ShiftedClass := function ( el )

      local  g, c, m, r, res, e;

      e := One(R);
      for g in el do
        c := Coefficients(g); m := Modulus(g);
        res := Filtered( AllResidues(R,m), r ->    c[r+1]{[1,3]} = [e,e]
                                               and not IsZero(c[r+1][2])
                                               and IsZero(c[r+1][2] mod m) );
        if res <> [] then
          r := res[1]; m := StandardAssociate(R,c[r+1][2]);
          Info(InfoRCWA,1,"The cyclic group generated by ",g," acts ",
                          "transitively on the residue class ",r,
                          "(",m,")."); 
          return ResidueClass(R,m,r);
        fi;
      od;
      return fail;
    end;

    ShiftedClassPowers := function ( el )

      local  g, m, cl, exp, pow, n, e;

      exp := [2,2,3,5,2,7,3,2,11,13,5,3,17,19,2];
      for g in el do
        pow := g; m := Modulus(g); e := 1;
        for n in exp do
          if Length(AllResidues(R,Modulus(pow))) > 4*Length(AllResidues(R,m))
          then break; fi;
          pow := pow^n; e := e * n;
          cl := ShiftedClass([pow]);
          if cl <> fail then return cl; fi;
        od;
      od;
      return fail;
    end;

    R := Source(One(G));
    if not IsSubset(R,S) then TryNextMethod(); fi;
    if   not ForAll(GeneratorsOfGroup(G),g->S^g=S)
    then Error("IsTransitive: <G> must act on <S>.\n"); fi;
    Info(InfoRCWA,1,"IsTransitive: ",
                    "testing for finiteness and searching short orbits ...");
    if   HasIsFinite(G) and IsFinite(G)
    then Info(InfoRCWA,1,"The group is finite."); return false; fi;
    if   (IsModularRcwaGroup(G) or IsZ_pi(R))
      and IsFinitelyGeneratedGroup(G) and HasIsTame(G) and IsTame(G)
    then return false; fi;
    if   IsIntegers(R) or IsZ_pi(R)
    then ranges := [[-10..10],[-30..30],[-100..100]];
    elif IsPolynomialRing(R) then
      x := IndeterminatesOfPolynomialRing(R)[1];
      ranges := [AllResidues(R,x^2),AllResidues(R,x^3),
                 AllResidues(R,x^4),AllResidues(R,x^6)];
    fi;
    ranges := List(ranges,range->Intersection(range,S));
    for range in ranges do
      if ShortOrbitsFound(range,4*Length(range)) then return false; fi;
    od;
    if   IsFinite(G)
    then Info(InfoRCWA,1,"The group is finite."); return false; fi;
    if   (IsModularRcwaGroup(G) or IsZ_pi(R))
      and IsFinitelyGeneratedGroup(G) and IsTame(G)
    then return false; fi;
    if IsIntegers(R) then 
      Info(InfoRCWA,1,"Searching for class shifts ...");
      Info(InfoRCWA,2,"... in generators");
      gen := GeneratorsOfGroup(G); cl := ShiftedClass(gen);
      if cl <> fail then return OrbitUnion(G,cl) = S; fi;
      Info(InfoRCWA,2,"... in commutators of the generators");
      comm := List(Combinations(gen,2),g->Comm(g[1],g[2]));
      cl := ShiftedClass(comm);
      if cl <> fail then return OrbitUnion(G,cl) = S; fi;
      Info(InfoRCWA,2,"... in powers of the generators");
      cl := ShiftedClassPowers(gen);
      if cl <> fail then return OrbitUnion(G,cl) = S; fi;
      Info(InfoRCWA,2,"... in powers of the commutators of the generators");
      cl := ShiftedClassPowers(comm);
      if cl <> fail then return OrbitUnion(G,cl) = S; fi;
      gen := Union(gen,List(gen,Inverse)); el := gen; WordLng := 1;
      repeat
        WordLng := WordLng + 1;
        Info(InfoRCWA,2,"... in powers of words of length ",WordLng,
                        " in the generators");
        el := Union(el,Flat(List(el,g->g*gen)));
        cl := ShiftedClassPowers(el);
        if cl <> fail then return OrbitUnion(G,cl) = S; fi;
      until false;
    else
      Info(InfoRCWA,1,"... this method gives up ...");
      TryNextMethod();
    fi;
  end );

#############################################################################
##
#M  Transitivity( <G>, Integers ) . . . . . . . . for rcwa group over Z and Z
#M  Transitivity( <G>, NonnegativeIntegers )
#M  Transitivity( <G>, PositiveIntegers )
##
##  This method might fail or run into an infinite loop.
##
InstallOtherMethod( Transitivity,
                    "for rcwa group over Z and one of Z, N_0 or N (RCWA)",
                    ReturnTrue, [ IsIntegralRcwaGroup, IsCollection ], 0,

  function ( G, D )

    local  gens, g, tups, tup, tupslng, invpairs, max, dom, finorb,
           stab, stabelm, decs, dec, decsp, decsm, bound, trs,
           S0, S, S_old, old_S, maxind, orb, oldorb, k, l, l0, m, str, i, j;

    if not (   IsIntegers(D) or IsNonnegativeIntegers(D)
            or IsPositiveIntegers(D))
    then TryNextMethod(); fi;

    gens := Set(GeneratorsAndInverses(G));
    invpairs := List([1..Length(gens)],i->[i,Position(gens,gens[i]^-1)]);

    if   IsIntegers(D)
    then Info(InfoRCWA,1,"Testing whether the group is tame ..."); fi;

    # Tame groups act at most 1-transitive.
    if IsIntegers(D) and IsTame(G) then
      Info(InfoRCWA,1,"Transitivity: The group is tame, and tame groups");
      Info(InfoRCWA,1,"can act at most 1-transitive on Z.");
      if IsTransitive(G,Integers) then return 1; else return 0; fi;
    fi;

    if HasIsTame(G) then
      if IsTame(G) then Info(InfoRCWA,1,"The group is tame.");
                   else Info(InfoRCWA,1,"The group is wild."); fi;
    fi;

    # Only class-wise order-preserving groups can act on N or N_0.
    if not IsIntegers(D) and not IsClassWiseOrderPreserving(G) then
      Info(InfoRCWA,1,"Transitivity: The group is not class-wise ",
                      "order-preserving,");
      Info(InfoRCWA,1,"thus does not act on ",D,".");
      return fail;
    fi;

    # If D = N or N_0: Check whether images under generators can be negative.
    if not IsIntegers(D) then
      max := -Minimum(List(gens,g->Minimum(List(Coefficients(g),c->c[2]))));
      if IsPositiveIntegers(D) then dom := [1..max];
                               else dom := [0..max]; fi;
      if not ForAll(gens,g->IsSubset(D,dom^g)) then
        Info(InfoRCWA,1,"Transitivity: The group does not act on ",D,".");
        return fail;
      fi;
    fi;

    # If whole residue classes are fixed, the action cannot be transitive.
    if Size(Difference(Integers,MovedPoints(G))) = infinity then
      Info(InfoRCWA,1,"Transitivity: The group fixes a residue class.");
      return 0;
    fi;

    # Check whether there are obvious finite orbits.
    finorb := ShortOrbits(G,Intersection([-144..144],D),36);
    if finorb <> [] then
      Info(InfoRCWA,1,"Transitivity: There are finite orbits.");
      Info(InfoRCWA,2,"These are e.g. ",finorb);
      return 0;
    fi;

    k := 1; tupslng := 2;

    while true do

      Info(InfoRCWA,1,"Transitivity: Checking for ",k,"-transitivity ...");

      tups := Concatenation(List([1..tupslng],
                                 k->Tuples([1..Length(gens)],k)));
      tups := Filtered(tups,
                       tup->ForAll(invpairs,
                                   pair->PositionSublist(tup,pair)=fail));

      Info(InfoRCWA,2,"There are ",Length(tups)," tuples of generators ",
                      "of length at most ",tupslng,".");

      if k = 1 then
        Info(InfoRCWA,2,"Computing their products ... ");
        stab := tups;
      else
        stab := [];
        if   IsPositiveIntegers(D)
        then l0 := [1..k-1]; else l0 := [0..k-2]; fi;
        for tup in tups do
          l := l0;
          for i in tup do l := List(l,n->n^gens[i]); od;
          if l = l0 then Add(stab,tup); fi;
        od;
        if IsPositiveIntegers(D) then
          if   k = 2 then str := "1"; elif k = 3 then str := "1 and 2";
          elif k = 4 then str := "1, 2 and 3";
          else str := Concatenation("1, 2, ... , ",String(k-1)); fi;
        else
          if   k = 2 then str := "0"; elif k = 3 then str := "0 and 1";
          elif k = 4 then str := "0, 1 and 2";
          else str := Concatenation("0, 1, ... , ",String(k-2)); fi;
        fi;
        Info(InfoRCWA,2,"The products of ",
                        Length(stab)," of these stabilize ",str,".");
        if stab = [] then
          Info(InfoRCWA,2,"Increment maximum generator tuple length ...");
          tupslng := tupslng + 1;
          continue;
        fi;
        Info(InfoRCWA,2,"Computing stabilizer elements ... ");
      fi;

      stabelm := List(stab,tup->Product(List(tup,i->gens[i])));
      Info(InfoRCWA,2,"The moduli of the computed stabilizer elements are\n",
                      List(stabelm,Modulus));
      Info(InfoRCWA,2,"Computing sets on which they are `decreasing' ... ");
      decs := List(stabelm,DecreasingOn);
      SortParallel(decs,stabelm,
        function(S1,S2)
          if   S1 = [] or S2 = [] then return false;
          else return First([1..100],k->Factorial(k) mod Modulus(S1) = 0)
                    < First([1..100],k->Factorial(k) mod Modulus(S2) = 0);
          fi;
        end);

      Info(InfoRCWA,2,"The moduli of the sets on which they are ",
                      "`decreasing' are\n",List(decs,Modulus));
      Info(InfoRCWA,2,"Checking whether the union of these sets is Z,");
      Info(InfoRCWA,2,"by successively subtracting them from Z.");

      S := Integers;
      for i in [1..Length(decs)] do
        S_old := S; S := Difference(S,decs[i]);
        if InfoLevel(InfoRCWA) >= 2 and S <> S_old then
          Print(i,": "); ViewObj(S); Print("\n");
        fi;
        if S = [] then maxind := i; break; fi;
      od;

      if S <> [] then

        Info(InfoRCWA,2,"Their union is NOT the whole of Z.");

        if not IsBound(old_S) or S <> old_S or Length(tups) < 10000 then
          Info(InfoRCWA,2,"Increment maximum generator tuple length ...");
          tupslng := tupslng + 1;
          old_S := S;
          continue;
        fi;

        Info(InfoRCWA,2,"Looking which numbers can be `decreased' ",
                        "additively ...");

        bound := Maximum(List(stabelm,
                              f->Maximum(List(Coefficients(f),
                                              c->AbsInt(c[2])))));
        bound := Maximum(bound,k+1,Lcm(List(stabelm,Modulus)));
        Info(InfoRCWA,2,"Bound = ",bound);

        decsp := List(stabelm,elm->Filtered([bound+1..2*bound],n->n^elm<n));
        trs := Union(decsp) = [bound+1..2*bound];
        if IsIntegers(D) and trs then
          decsm := List(stabelm,
                        elm->Filtered([-2*bound..-bound-1],n->n^elm>n));
          if Union(decsm) <> [-2*bound..-bound-1] then trs := false; fi;
        fi;

        if trs then

          Info(InfoRCWA,2,"Numbers larger than ",bound," can be decreased.");
          Info(InfoRCWA,2,"Checking smaller numbers ...");
          if IsPositiveIntegers(D) then S := [k]; else S := [k-1]; fi;
          S0 := Intersection(D,[-bound..bound]);
          if IsPositiveIntegers(D) then S0 := Difference(S0,[1..k-1]);
                                   else S0 := Difference(S0,[0..k-2]); fi;
          repeat
            S_old := ShallowCopy(S);
            for g in stabelm do
              S := Union(S,S^g);
              Info(InfoRCWA,1,"|S| = ",Length(S),".");
              if IsSubset(S,S0) then break; fi;
            od;
          until IsSubset(S,S0) or S = S_old;

          if IsSubset(S,S0) then
            Info(InfoRCWA,1,"Transitivity: ",k,
                            " - transitivity has been proved.");
            k := k + 1;
            continue;
          else trs := false; fi;

        fi;

        m := Lcm(List(gens,Modulus)) * Lcm(List(gens,Divisor));
        if m^k >= 1000000 then
          Info(InfoRCWA,1,"Can neither prove nor disprove ",k,
                          " - transitivity. Giving up.");
          return Concatenation("At least ",String(k-1),
                               ", but otherwise don't know.");
        fi;

        Info(InfoRCWA,2,"Checking transitivity on ",k,
                        " - tuples (mod ",m,") ...");
        orb := [[1..k]];;
        repeat
          Info(InfoRCWA,2,"Orbit length >= ",Length(orb),".");
          oldorb := ShallowCopy(orb);
          for g in gens do
            orb := Union(orb,List(orb,l->List(l,n->n^g) mod m));
          od;
        until orb = oldorb;

        if Length(orb) < m^k then
          Info(InfoRCWA,2,"The action is not transitive on ",k,
                          " - tuples (mod ",m,").");
          Info(InfoRCWA,1,"Transitivity: ",k,
                          " - transitivity has been disproved.");
          return k-1;
        else
          Info(InfoRCWA,2,"The action is transitive on ",k,
                          " - tuples (mod ",m,").");
          Info(InfoRCWA,1,"Can neither prove nor disprove ",k,
                          " - transitivity. Giving up.");
          return Concatenation("At least ",String(k-1),
                               ", but otherwise don't know.");
        fi;

      else

        bound := Maximum(List(stabelm{[1..maxind]},
                         f->Maximum(List(Coefficients(f),c->c[2]))));
        Info(InfoRCWA,1,"The upper bound on `small' points is ",bound,".");

        if IsPositiveIntegers(D) then S := [k]; else S := [k-1]; fi;
        S0 := Intersection(D,[-bound..bound]);
        if IsPositiveIntegers(D) then S0 := Difference(S0,[1..k-1]);
                                 else S0 := Difference(S0,[0..k-2]); fi;
        repeat
          S_old := ShallowCopy(S);
          for g in stabelm do
            S := Union(S,S^g);
            Info(InfoRCWA,1,"|S| = ",Length(S),".");
            if IsSubset(S,S0) then break; fi;
          od;
        until IsSubset(S,S0) or S = S_old;

        if not IsSubset(S,S0) then
          Info(InfoRCWA,1,"Not all points below the bound ",
                          "lie in one orbit.");
          Info(InfoRCWA,1,"This means that the action is not ",k,
                          " - transitive.");
          return k - 1;
        fi;

        Info(InfoRCWA,1,"All points below the bound lie in one orbit.");
        Info(InfoRCWA,1,"This means that ",k,
                        " - transitivity has been proved.");

        k := k + 1;

      fi;

    od;

  end );

#############################################################################
##
#M  IsPrimitive( <G>, <S> ) . . . . .  for rcwa group and residue class union
##
##  This method might fail or run into an infinite loop.
##
InstallOtherMethod( IsPrimitive,
                    "for rcwa group and residue class union (RCWA)",
                    ReturnTrue, [ IsIntegralRcwaGroup,
                                  IsListOrCollection ], 0,

  function ( G, S )

    if not IsSubset(Source(One(G)),S) then TryNextMethod(); fi;
    if   not ForAll(GeneratorsOfGroup(G),g->S^g=S)
    then Error("IsPrimitive: <G> must act on <S>.\n"); fi;
    if not IsTransitive(G,S) or IsTame(G) then return false; fi;
    TryNextMethod(); # Conjecture: true.
  end );

#############################################################################
##
#M  OrbitOp( <G>, <pnt>, <gens>, <acts>, <act> )
##
InstallOtherMethod( OrbitOp,
                    "for tame integral rcwa groups (RCWA)", ReturnTrue,
                    [ IsIntegralRcwaGroup, IsInt, IsList, IsList,
                      IsFunction ], 0,

  function ( G, pnt, gens, acts, act )

    local  P, M, where, delta, S, orb;

    if act <> OnPoints then TryNextMethod(); fi;
    orb := ShortOrbits(G,[pnt],100);
    if orb <> [] then return orb[1]; fi;
    if IsFinite(G) or not IsTame(G) then TryNextMethod(); fi;
    P := RespectedPartition(G);
    M := KernelOfActionOnRespectedPartitionHNFMat(G);
    if M <> [] then
      where := First([1..Length(P)],pos->pnt in P[pos]);
      delta := List(TransposedMat(M),Gcd)[where];
      if delta <> 0 then S := ResidueClass(Integers,delta,pnt);
                    else TryNextMethod(); fi;
    else TryNextMethod(); fi;
    return OrbitUnion(G,S);
  end );

#############################################################################
##
#M  EpimorphismFromFreeGroup( <G> ) . . . . . . . . . . . . .  for rcwa group
##
InstallMethod( EpimorphismFromFreeGroup,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  F, gens, gensnames, i;

    gens := GeneratorsOfGroup(G); gensnames := [];
    for i in [1..Length(gens)] do
      if   HasName(gens[i])
      then Add(gensnames,Name(gens[i]));
      else Add(gensnames,Concatenation("f",String(i))); fi;
    od;
    F := FreeGroup(gensnames);
    return EpimorphismByGenerators(F,G);
  end );

#############################################################################
##
#M  RepresentativesActionPreImage( <G>, <src>, <dest>, <act>, <F> )
##
InstallMethod( RepresentativesActionPreImage,
               "for rcwa groups and permutation groups (RCWA)", ReturnTrue,
               [ IsGroup, IsObject, IsObject, IsFunction, IsFreeGroup ],
               0,

  function ( G, src, dest, act, F )

    local  SetOfRepresentatives, Extended, R, gensG, gensF, 
           orbsrc, orbdest, g, extstep, oldorbsizes,
           inter, intersrc, interdest, compatible;

    SetOfRepresentatives := function ( S, rel, less, pref )

      local  reps, elm, pos;

      if IsEmpty(S) then return []; fi;
      Sort(S,less); reps := [S[1]]; pos := 1;
      for elm in S do
        if rel(elm,reps[pos]) then
          if pref(elm,reps[pos]) then reps[pos] := elm; fi;
        else
          pos := pos + 1;
          reps[pos] := elm;
        fi;
      od;
      return reps;
    end;

    Extended := function ( orb, gens )

      local  eq, lt, shorter, nextlayer, g;

      nextlayer := List(gens,g->List(orb,t->[act(t[1],g),
                                     t[2]*gensF[Position(gensG,g)]]));
      orb := Union(Concatenation([orb],nextlayer));
      eq := function(t1,t2) return t1[1] = t2[1]; end;
      lt := function(t1,t2) return t1[1] < t2[1]; end;
      shorter := function(t1,t2) return Length(t1[2]) < Length(t2[2]); end;
      return SetOfRepresentatives(orb,eq,lt,shorter);
    end;

    if   IsPermGroup(G)
    then R := PositiveIntegers;
    elif IsRcwaGroup(G) then R := Source(One(G));
    else TryNextMethod(); fi;
    if not IsList(src)  then src  := [src];  fi;
    if not IsList(dest) then dest := [dest]; fi;
    if   not IsSubset(R,Union(src,dest))
      or Length(GeneratorsOfGroup(G)) <> Length(GeneratorsOfGroup(F))
    then TryNextMethod(); fi;
    if Length(src) <> Length(dest) then return []; fi;
    gensF := GeneratorsAndInverses(F); gensG := GeneratorsAndInverses(G);
    orbsrc := [[src,One(F)]]; orbdest := [[dest,One(F)]]; extstep := 0;
    repeat
      oldorbsizes := [Length(orbsrc),Length(orbdest)];
      orbsrc := Extended(orbsrc,gensG); orbdest := Extended(orbdest,gensG);
      extstep := extstep + 1;
      Info(InfoRCWA,2,"Orbit lengths after extension step ",extstep,": ",
                      [Length(orbsrc),Length(orbdest)]);
      if Maximum(Length(orbsrc),Length(orbdest)) < 100 then
        Info(InfoRCWA,3,"Orbits after extension step ",extstep,":\n",
                        orbsrc,"\n",orbdest);
      fi;
      inter := Intersection(List(orbsrc,t->t[1]),List(orbdest,t->t[1]));
    until inter <> [] or oldorbsizes = [Length(orbsrc),Length(orbdest)];
    if inter = [] then return []; fi;
    intersrc   := Filtered(orbsrc, t->t[1] in inter);
    interdest  := Filtered(orbdest,t->t[1] in inter);
    compatible := Filtered(Cartesian(intersrc,interdest),t->t[1][1]=t[2][1]);
    Info(InfoRCWA,2,"|Candidates| = ",Length(compatible));
    return Set(List(compatible,t->t[1][2]*t[2][2]^-1));
  end );

#############################################################################
##
#M  RepresentativeActionPreImage( <G>, <src>, <dest>, <act>, <F> )
##
InstallMethod( RepresentativeActionPreImage,
               "for rcwa groups and permutation groups (RCWA)", ReturnTrue,
               [ IsGroup, IsObject, IsObject, IsFunction, IsFreeGroup ],
               0,

  function ( G, src, dest, act, F )

    local  candidates, minlng, shortest;

    if not IsRcwaGroup(G) and not IsPermGroup(G) then TryNextMethod(); fi;
    candidates := RepresentativesActionPreImage(G,src,dest,act,F);
    if candidates = [] then return fail; fi;
    minlng   := Minimum(List(candidates,Length));
    shortest := Filtered(candidates,cand->Length(cand)=minlng)[1];
    return shortest;
  end );

#############################################################################
##
#M  RepresentativeActionOp( <G>, <src>, <dest>, <act> )
##
InstallOtherMethod( RepresentativeActionOp,
                    "for rcwa groups (RCWA)", ReturnTrue,
                    [ IsRcwaGroup, IsObject, IsObject, IsFunction ], 0,

  function ( G, src, dest, act )

    local  F, phi, pre;

     phi := EpimorphismFromFreeGroup(G);
     pre := RepresentativeActionPreImage(G,src,dest,act,Source(phi));
     if pre = fail then return fail; fi;
     return pre^phi;
  end );

#############################################################################
##
#M  PreImagesRepresentatives( <phi>, <g> )
##
InstallMethod( PreImagesRepresentatives,
               "for hom's from free groups to integral rcwa groups (RCWA)",
               ReturnTrue, [ IsGroupHomomorphism, IsObject ], 0,

  function ( phi, g )

    local  F, G, IsCorrect, candidates, minlng, shortest,
           preimage, image, lng, add;

    IsCorrect := function ( cand )

      local  gens, letters, factors, f, n, m;

      gens    := GeneratorsOfGroup(G);
      letters := LetterRepAssocWord(cand);
      factors := List(letters,i->gens[AbsInt(i)]^SignInt(i));
      for n in [1..3*Length(letters)] do
        m := n; for f in factors do m := m^f; od;
        if m <> n^g then return false; fi;
      od;
      return cand^phi = g;
    end;

    F := Source(phi); G := Range(phi);
    if   not IsFreeGroup(F)
      or not (IsIntegralRcwaGroup(G) or IsPermGroup(G))
      or FamilyObj(g) <> FamilyObj(One(G))
      or MappingGeneratorsImages(phi) <> List([F,G],GeneratorsOfGroup)
    then TryNextMethod(); fi;
    lng := 1; add := 1;
    repeat
      lng        := lng + add; if IsPermGroup(G) then add := add + 1; fi;
      preimage   := [1..lng];
      image      := List(preimage,n->n^g);
      candidates := RepresentativesActionPreImage(G,preimage,image,
                                                  OnTuples,F);
      if candidates = [] then return []; fi;
      candidates := Filtered(candidates,IsCorrect);
    until candidates <> [];
    return candidates;
  end );

#############################################################################
##
#M  PreImagesRepresentative( <phi>, <g> )
##
InstallMethod( PreImagesRepresentative,
               "for hom's from free groups to rcwa- or perm.-groups (RCWA)",
               ReturnTrue, [ IsGroupHomomorphism, IsObject ], SUM_FLAGS,

  function ( phi, g )

    local  candidates, minlng, shortest;

    if not IsRcwaMapping(g) and
       not (IsPerm(g) and ValueOption("NoStabChain") = true)
    then TryNextMethod(); fi;
    candidates := PreImagesRepresentatives(phi,g);
    if candidates = [] then return fail; fi;
    minlng   := Minimum(List(candidates,Length));
    shortest := Filtered(candidates,cand->Length(cand)=minlng)[1];
    return shortest;
  end );

#############################################################################
##
#M  Factorization( <G>, <g> ) . . . . . . .  for rcwa mappings in rcwa groups
##
if IsOperation( Factorization ) then  # In GAP 4.5 or higher.
  InstallMethod( Factorization,
                 "for rcwa mappings in rcwa groups (RCWA)", true,
                 [ IsRcwaGroup, IsRcwaMapping ], 0,

    function ( G, g )
      return PreImagesRepresentative(EpimorphismFromFreeGroup(G),g);
    end );
fi;

#############################################################################
##
#M  IsSolvable( <G> ) . . . . . . . . . . . . . . . . . . . . for rcwa groups
##
InstallMethod( IsSolvable,
               "for rcwa groups (RCWA)", ReturnTrue, [ IsRcwaGroup ], 0,

  function ( G )
    if IsAbelian(G) then return true; fi;
    if not IsTame(G) then TryNextMethod(); fi;
    return IsSolvable(ActionOnRespectedPartition(G));
  end );

#############################################################################
##
#M  IsPerfect( <G> ) . . . . . . . . . . . . . . . . . . . .  for rcwa groups
##
InstallMethod( IsPerfect,
               "for rcwa groups (RCWA)", ReturnTrue, [ IsRcwaGroup ], 0,

  function ( G )
    if IsTrivial(G) then return true; fi;
    if IsAbelian(G) then return false; fi;
    if IsIntegralRcwaGroup(G) then
      if   ForAny(GeneratorsOfGroup(G),g->Sign(g)<>1)
        or (     IsClassWiseOrderPreserving(G)
             and ForAny(GeneratorsOfGroup(G),g->Determinant(g)<>0))
      then return false; fi;
    fi;
    if not IsTame(G) then TryNextMethod(); fi;
    return IsPerfect(ActionOnRespectedPartition(G));
  end );

#############################################################################
##
#F  NrConjugacyClassesOfRCWAZOfOrder( <ord> ) . #Ccl of RCWA(Z) / order <ord>
##
InstallGlobalFunction( NrConjugacyClassesOfRCWAZOfOrder,

  function ( ord )

    if   not IsPosInt(ord) then return 0;
    elif ord = 1 then return 1;
    elif ord mod 2 = 0 then return infinity;
    else return Length(Filtered(Combinations(DivisorsInt(ord)),
                                l -> l <> [] and Lcm(l) = ord));
    fi;
  end );

#############################################################################
##
#M  Restriction( <G>, <f> ) . . . . . . . . . . . . . . . . . for rcwa groups
##
InstallOtherMethod( Restriction,
                    "RCWA: for rcwa groups (RCWA)", ReturnTrue,
                    [ IsRcwaGroup, IsRcwaMapping ], 0,

  function ( G, f )

    local Gf;

    if   Source(One(G)) <> Source(f) or not IsInjective(f)
    then return fail; fi;

    Gf := GroupByGenerators(List(GeneratorsOfGroup(G),g->Restriction(g,f)));

    if HasIsTame(G) then SetIsTame(Gf,IsTame(G)); fi;
    if HasSize(G)   then SetSize(Gf,Size(G)); fi;

    return Gf;
  end );

#############################################################################
##
#M  DirectProductOp( <groups>, <onegroup> ) . . . .  for integral rcwa groups
##
InstallMethod( DirectProductOp,
               "for integral rcwa groups (RCWA)", ReturnTrue,
               [ IsList, IsIntegralRcwaGroup ], 0,

  function ( groups, onegroup )

    local  D, factors, f, m, G, gens, info, first;

    if   IsEmpty(groups) or not ForAll(groups,IsIntegralRcwaGroup)
    then TryNextMethod(); fi;
    m := Length(groups);
    f := List([0..m-1],r->RcwaMapping([[m,r,1]]));
    factors := List([1..m],r->Restriction(groups[r],f[r]));
    gens := []; first := [1];
    for G in factors do
      gens := Concatenation(gens,GeneratorsOfGroup(G));
      Add(first,Length(gens)+1);
    od;

    D := GroupByGenerators(gens);
    info := rec(groups := groups, first := first,
                embeddings := [ ], projections := [ ]);
    SetDirectProductInfo(D,info);

    if   ForAll(groups,HasIsTame) and ForAll(groups,IsTame)
    then SetIsTame(D,true); fi;
    if   ForAny(groups,grp->HasIsTame(grp) and not IsTame(grp))
    then SetIsTame(D,false); fi;
    if   ForAny(groups,grp->HasSize(grp) and Size(grp) = infinity)
    then SetSize(D,infinity); fi;
    if   ForAll(groups,grp->HasSize(grp) and IsInt(Size(grp)))
    then SetSize(D,Product(List(groups,Size))); fi;

    return D;
  end );

#############################################################################
##
#M  ViewObj( <RG> ) . . . . . . . . . . . . . .  for group ring of rcwa group
##
InstallMethod( ViewObj,
               "for group rings of rcwa groups (RCWA)",
               ReturnTrue, [ IsGroupRing ], 100,

  function ( RG )

    local  R, G;

    R := LeftActingDomain(RG); G := UnderlyingGroup(RG);
    if not IsRcwaGroup(G) or R <> Source(One(G)) then TryNextMethod(); fi;
    Print(RingToString(R)," "); ViewObj(G);
  end );

#############################################################################
##
#M  ViewObj( <elm> ) . . . . . . . .  for element of group ring of rcwa group
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
#E  rcwagrp.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here