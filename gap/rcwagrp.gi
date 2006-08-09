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

# Some implications.

InstallTrueMethod( IsGroup,     IsRcwaGroup );
InstallTrueMethod( IsRcwaGroup, IsRcwaGroupOverZOrZ_pi );
InstallTrueMethod( IsRcwaGroupOverZOrZ_pi, IsRcwaGroupOverZ );
InstallTrueMethod( IsRcwaGroupOverZOrZ_pi, IsRcwaGroupOverZ_pi );
InstallTrueMethod( IsRcwaGroup, IsRcwaGroupOverGFqx );

#############################################################################
##
#M  IsGeneratorsOfMagmaWithInverses( <l> ) . . .  for a list of rcwa mappings
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
#V  TrivialRcwaGroupOverZ( <G> ) . . . . . . . . .  trivial rcwa group over Z
#V  TrivialRcwaGroup( <G> )
##
InstallValue( TrivialRcwaGroupOverZ, Group( IdentityRcwaMappingOfZ ) );

#############################################################################
##
#M  TrivialSubmagmaWithOne( <G> ). . . . . . . . . . . . . .  for rcwa groups
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
#V  RcwaGroupsOverZFamily . . . . . . . the family of all rcwa groups over Z
##
BindGlobal( "RcwaGroupsOverZFamily", FamilyObj( TrivialRcwaGroupOverZ ) );

#############################################################################
##
#M  RCWACons( IsRcwaGroup, Integers ) . . . . . . . . . . . . . . . RCWA( Z )
##
##  Group formed by all bijective rcwa mappings of $\Z$.
##
InstallMethod( RCWACons,
               "natural RCWA(Z) (RCWA)", true,
               [ IsRcwaGroup, IsIntegers ], 0,

  function ( filter, R )

    local  G;

    G := Objectify( NewType( RcwaGroupsOverZFamily,
                             IsRcwaGroupOverZ and IsAttributeStoringRep ),
                    rec( ) );
    SetIsTrivial( G, false );
    SetOne( G, IdentityRcwaMappingOfZ );
    SetIsNaturalRCWA_Z( G, true );
    SetModulusOfRcwaGroup( G, 0 );
    SetMultiplier( G, infinity );
    SetDivisor( G, infinity );
    SetIsFinite( G, false ); SetSize( G, infinity );
    SetIsFinitelyGeneratedGroup( G, false );
    SetCentre( G, TrivialRcwaGroupOverZ );
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
                                  IsRcwaGroupOverZ_pi
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
                                  IsRcwaGroupOverGFqx
                              and IsAttributeStoringRep ),
                     rec( ) );
    SetIsTrivial( G, false );
    SetOne( G, id );
    SetIsNaturalRCWA_GFqx( G, true );
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
#M  IsNaturalRCWA_GFqx( <G> ) . . . . . . . . . . . . . . . .  RCWA(GF(q)[x])
##
##  The groups RCWA(GF(q)[x]) can only be obtained by the above constructor.
##
InstallMethod( IsNaturalRCWA_GFqx,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               ReturnFalse );

#############################################################################
##
#M  IsSubset( <G>, <H> ) . . . . . . . . . . . . . for two rcwa groups over Z
##
InstallMethod( IsSubset,
               "for two rcwa groups over Z (RCWA)", true,
               [ IsRcwaGroupOverZ, IsRcwaGroupOverZ ], 0,

  function ( G, H )

    local  gensG, gensH, dG, dH;

    gensG := GeneratorsOfGroup(G); gensH := GeneratorsOfGroup(H);
    if IsSubset(gensG,gensH) then return true; fi;
    if not IsSubset(PrimeSet(G),PrimeSet(H)) then return false; fi;
    if   ForAll(gensG,g->Sign(g) = 1) and ForAny(gensH,h->Sign(h)=-1)
    then return false; fi;
    if IsClassWiseOrderPreserving(G) then
      if not IsClassWiseOrderPreserving(H) then return false; fi;
      dG := Gcd(List(gensG,Determinant));
      dH := Gcd(List(gensH,Determinant));
      if   dG = 0 and dH <> 0 or dG <> 0 and dH mod dG <> 0
      then return false; fi;
    fi;
    if IsTame(G) and not IsTame(H) then return false; fi;
    if IsTame(G) and IsTame(H) then
      if Multiplier(G) mod Multiplier(H) <> 0 then return false; fi;
      if   not RespectsPartition(H,RespectedPartition(G))
      then return false; fi;
      if not IsSubgroup(ActionOnRespectedPartition(G),
                        Action(H,RespectedPartition(G)))
      then return false; fi;
      if   Size(H) > Size(G)
        or RankOfKernelOfActionOnRespectedPartition(H)
         > RankOfKernelOfActionOnRespectedPartition(G)
      then return false; fi;
    fi;
    return ForAll(gensH,h->h in G);
  end );

#############################################################################
##
#M  CyclicGroupCons( IsRcwaGroupOverZ, <n> )
##
InstallOtherMethod( CyclicGroupCons,
                    "rcwa group over Z, for a positive integer (RCWA)",
                    ReturnTrue, [ IsRcwaGroupOverZ, IsPosInt ], 0,

  function( filt, n )

    local  result;

    if n = 1 then return TrivialRcwaGroupOverZ; fi;
    result := Image(IsomorphismRcwaGroupOverZ(CyclicGroup(IsPermGroup,n)));
    SetSize(result,n); SetIsCyclic(result,true);
    SetIsTame(result,true); SetIsIntegral(result,true);
    return result;
  end );

#############################################################################
##
#M  CyclicGroupCons( IsRcwaGroupOverZ, infinity )
##
InstallOtherMethod( CyclicGroupCons,
                    "(Z,+) as an rcwa group (RCWA)", ReturnTrue,
                    [ IsRcwaGroupOverZ, IsInfinity ], 0,

  function( filt, infty )

    local  result;

    result := Group(ClassShift(0,1));
    SetSize(result,infinity); SetIsCyclic(result,true);
    SetIsTame(result,true); SetIsIntegral(result,true);
    return result;
  end );

#############################################################################
##
#M  DihedralGroupCons( IsRcwaGroupOverZ, infinity )
##
InstallOtherMethod( DihedralGroupCons,
                    "the rcwa group < n |-> n+1, n |-> -n > (RCWA)",
                    ReturnTrue, [ IsRcwaGroupOverZ, IsInfinity ], 0,

  function( filt, infty )

    local  result;

    result := Group(ClassShift(0,1),ClassReflection(0,1));
    SetSize(result,infinity);
    SetIsTame(result,true); SetIsIntegral(result,true);
    return result;
  end );

#############################################################################
##
#M  AbelianGroupCons( IsRcwaGroupOverZ, <invs> )
##
InstallOtherMethod( AbelianGroupCons,
                    "rcwa group over Z, for list of abelian inv's (RCWA)",
                    ReturnTrue, [ IsRcwaGroupOverZ, IsList ], 0,

  function( filt, invs )

    local  result;

    if not ForAll(invs,n->IsInt(n) or n=infinity) then TryNextMethod(); fi;
    result := DirectProduct(List(invs,n->CyclicGroup(IsRcwaGroupOverZ,n)));
    SetSize(result,Product(invs)); SetIsAbelian(result,true);
    SetIsTame(result,true); SetIsIntegral(result,true);
    return result;
  end );

#############################################################################
##
#M  IsSolvable( <G> ) . . . . . . . . . . . . . . . default method for groups
##
InstallMethod( IsSolvable,
               "default method for groups (RCWA)", true, [ IsGroup ],
               SUM_FLAGS,

  function ( G )
    if   HasIsSolvableGroup(G)
    then return IsSolvableGroup(G);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  IsPerfect( <G> ) . . . . . . . . . . . . . . .  default method for groups
##
InstallMethod( IsPerfect,
               "default method for groups (RCWA)", true, [ IsGroup ],
               SUM_FLAGS,

  function ( G )
    if   HasIsPerfectGroup(G)
    then return IsPerfectGroup(G);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  IsSimple( <G> ) . . . . . . . . . . . . . . . . default method for groups
##
InstallMethod( IsSimple,
               "default method for groups (RCWA)", true, [ IsGroup ],
               SUM_FLAGS,

  function ( G )
    if   HasIsSimpleGroup(G)
    then return IsSimpleGroup(G);
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#F  ClassPairs( <m> )
##
##  All pairs of disjoint residue classes with modulus < m.
##
InstallGlobalFunction( ClassPairs,
  m -> Filtered(Cartesian([0..m-1],[1..m],[0..m-1],[1..m]),
                t -> t[1] < t[2] and t[3] < t[4] and t[2] <= t[4]
                     and (t[1]-t[3]) mod Gcd(t[2],t[4]) <> 0
                     and (t[2] <> t[4] or t[1] < t[3])) );

InstallValue( CLASS_PAIRS, [ 6, ClassPairs(6) ] );
InstallValue( CLASS_PAIRS_LARGE, CLASS_PAIRS );

#############################################################################
##
#M  Random( RCWA( Integers ) ) . . . . . . . .  a `random' element of RCWA(Z)
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
    if not tame then SetFactorizationIntoCSCRCT(Result,GenFactors); fi;
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
#M  \in( <g>, RCWA( Integers ) ) . . . . for an rcwa mapping of Z and RCWA(Z)
##
InstallMethod( \in,
               "for an rcwa mapping of Z and RCWA(Z) (RCWA)", ReturnTrue,
               [ IsRcwaMappingOfZ, IsNaturalRCWA_Z ], 100,

  function ( g, G )
    return IsBijective(g);
  end );

#############################################################################
##
#M  \in( <g>, RCWA( Z_pi( <pi> ) ) ) . . for an rcwa mapping and RCWA(Z_(pi))
##
InstallMethod( \in,
               "for rcwa mapping of Z or Z_(pi) and RCWA(Z_(pi)) (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZ_pi, IsNaturalRCWA_Z_pi ], 100,

  function ( g, G )
    return FamilyObj(g) = FamilyObj(One(G)) and IsBijective(g);
  end );

#############################################################################
##
#M  \in( <g>, RCWA( GF(q)[x] ) ) . . . for an rcwa mapping and RCWA(GF(q)[x])
##
InstallMethod( \in,
               "for rcwa mapping of GF(q)[x] and RCWA(GF(q)[x]) (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfGFqx, IsNaturalRCWA_GFqx ],
               100,

  function ( g, G )
    return FamilyObj(g) = FamilyObj(One(G)) and IsBijective(g);
  end );

#############################################################################
## 
#M  IsSubset( RCWA( Integers ), G ) . .  for RCWA(Z) and an rcwa group over Z
## 
InstallMethod( IsSubset,
               "for RCWA(Z) and an rcwa group over Z (RCWA)", ReturnTrue,
               [ IsNaturalRCWA_Z, IsRcwaGroupOverZ ], 0, ReturnTrue );

#############################################################################
##
#M  IsSubset( RCWA( Z_pi( <pi> ) ), G ) . .  for RCWA(Z_pi) and an rcwa group
##
InstallMethod( IsSubset,
               "for RCWA(Z_(pi)) and an rcwa group over Z_(pi) (RCWA)",
               ReturnTrue, [ IsNaturalRCWA_Z_pi, IsRcwaGroupOverZ_pi ], 0,

  function ( RCWA_Z_pi, G )
    return FamilyObj(One(RCWA_Z_pi)) = FamilyObj(One(G));
  end );

#############################################################################
##
#M  IsSubset( RCWA( GF(q)[x] ), G ) . .  for RCWA(GF(q)[x]) and an rcwa group
##
InstallMethod( IsSubset,
               "for RCWA(GF(q)[x]) and an rcwa group over GF(q)[x] (RCWA)",
               ReturnTrue, [ IsNaturalRCWA_GFqx, IsRcwaGroupOverGFqx ], 0,

  function ( RCWA_GFqx, G )
    return FamilyObj(One(RCWA_GFqx)) = FamilyObj(One(G));
  end );

#############################################################################
##
#M  Display( RCWA( <R> ) ) . . . . . . . . . . . . . . . . . . .  for RCWA(R)
##
InstallMethod( Display,
               "for RCWA(R) (RCWA)", true, [ IsRcwaGroup and HasName ], 0,

  function ( G )
    if   IsNaturalRCWA_Z( G ) or IsNaturalRCWA_Z_pi( G )
      or IsNaturalRCWA_GFqx( G )
    then Print( Name( G ), "\n" ); else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  ViewObj( <G> ) . . . . . . . . . . . . . . . . . . . . .  for rcwa groups
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
#M  Display( <G> ) . . . . . . . . . . . . . . . . . . . . .  for rcwa groups
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
#M  MovedPoints( <G> ) . . . . . . . . . . . . . . . . . . .  for rcwa groups
##
##  The set of moved points (support) of the rcwa group <G>.
##
InstallOtherMethod( MovedPoints,
                    "for rcwa group (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )
    if IsNaturalRCWA_Z(G) or IsNaturalRCWA_Z_pi(G) or IsNaturalRCWA_GFqx(G)
    then return Source(One(G)); fi;
    return Union(List(GeneratorsOfGroup(G),MovedPoints));
  end );

#############################################################################
##
#M  Support( <G> ) . . . . . . . . . . . . . . . .  default method for groups
##
InstallMethod( Support,
               "default method for groups (RCWA)", true, [ IsGroup ], 0,
               MovedPoints );

#############################################################################
##
#M  IsomorphismRcwaGroupOverZ( <G> ) . . . . default method for finite groups
#M  IsomorphismRcwaGroup( <G> )
##
##  This is a simple method which just embeds <G> into Sym($\Z/m\Z$).
##
InstallMethod( IsomorphismRcwaGroupOverZ,
               "default method for finite groups (RCWA)", true,
               [ IsGroup and IsFinite ], 0,

  function ( G )

    local  G2, H, phi1, phi2, n;

    if IsRcwaGroupOverZ(G) then return IdentityMapping(G); fi;
    if   not IsPermGroup(G) 
    then phi1 := IsomorphismPermGroup(G); G2 := Image(phi1);
    else phi1 := IdentityMapping(G);      G2 := G; fi;
    n := LargestMovedPoint(G2);
    H := GroupWithGenerators(List(GeneratorsOfGroup(G2),
           g -> RcwaMapping(g,[1..n])))^(ClassShift(0,1)^-1);
    phi2 := GroupHomomorphismByImagesNC(G2,H,GeneratorsOfGroup(G2),
                                             GeneratorsOfGroup(H));
    return Immutable(CompositionMapping(phi2,phi1));
  end );

#############################################################################
##
#F  RcwaGroupOverZByPermGroup( <G> ) . an rcwa group over Z isomorphic to <G>
#F  RcwaGroupByPermGroup( <G> )
##
InstallGlobalFunction( RcwaGroupOverZByPermGroup,

  function ( G )

    local  H, phi, phi_1;

    if   not IsPermGroup(G) 
    then Error("<G> must be a permutation group"); fi;
    phi := IsomorphismRcwaGroupOverZ(G);
    H   := Image(phi);
    phi_1 := InverseGeneralMapping(phi);
    SetIsomorphismPermGroup(H,phi_1);
    SetNiceMonomorphism(H,phi_1);
    SetNiceObject(H,G);
    return H;
  end );

#############################################################################
##
#M  PrimeSet( <G> ) . . . . . . . . . . . . . . . . . . . . . for rcwa groups
##
InstallMethod( PrimeSet,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> Union( List( GeneratorsOfGroup( G ), PrimeSet ) ) );

#############################################################################
##
#M  IsIntegral( <G> ) . . . . . . . . . . . . . . . . . . . . for rcwa groups
##
InstallOtherMethod( IsIntegral,
                    "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0, 
                    G -> ForAll( GeneratorsOfGroup( G ), IsIntegral ) );

#############################################################################
##
#M  IsClassWiseOrderPreserving( <G> ) . . .  for rcwa groups over Z or Z_(pi)
##
##  We say that an rcwa group over $\Z$ or $\Z_{\pi}$ is *class-wise
##  order-preserving* if all of its elements are.
##
InstallOtherMethod( IsClassWiseOrderPreserving,
                    "for rcwa groups over Z or Z_(pi) (RCWA)",
                    true, [ IsRcwaGroupOverZOrZ_pi ], 0,
                    G -> ForAll( GeneratorsOfGroup( G ),
                                 IsClassWiseOrderPreserving ) );

#############################################################################
## 
#M  ShortOrbits( <G>, <S>, <maxlng> ) . . . . . . . . . . . . for rcwa groups
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
#M  OrbitsModulo( <G>, <m> ) . . . . . . . . for rcwa groups over Z or Z_(pi)
##
InstallOtherMethod( OrbitsModulo,
                    "for rcwa groups over Z or Z_(pi) (RCWA)", true,
                    [ IsRcwaGroupOverZOrZ_pi, IsPosInt ], 0,

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

#############################################################################
##
#M  Projections( <G>, <m> ) . . . . . . . . . . . . .  for rcwa groups over Z
##
InstallMethod( Projections,
               "for rcwa groups over Z (RCWA)", ReturnTrue,
               [ IsRcwaGroupOverZ, IsPosInt ], 0,

  function ( G, m )

    local  orbs, gens, groups;

    gens   := GeneratorsOfGroup(G);
    orbs   := List(OrbitsModulo(G,m),orb->ResidueClassUnion(Integers,m,orb));
    groups := List(orbs,orb->Group(List(gens,gen->RestrictedPerm(gen,orb))));
    return List(groups,grp->EpimorphismByGeneratorsNC(G,grp));
  end );

#############################################################################
##
#M  Modulus( <G> ) . . . . . . . . . . . . . . . . . . . . .  for rcwa groups
##
##  Modulus of the rcwa group <G>.
##
##  We define the modulus of an rcwa group <G> by the least common multiple
##  of the moduli of its elements.
##
InstallMethod( Modulus,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  CheckModulus,
           R, m, oldmod, maxfinmod, g, gens, els, step, maxstep;

    CheckModulus := function ( G, m )

      local  IsAffine, R, P, gens, errormessage;

      IsAffine := function ( g, cl )

        local  m, c, res, cls;

        m := Modulus(g); c := Coefficients(g); res := AllResidues(R,m);
        cls := Filtered(List(res,r->ResidueClass(R,m,r)),
                        clm->Intersection(clm,cl)<>[]);
        return Length(Set(c{List(cls,clm->Position(res,
                                                   Residues(clm)[1]))}))=1;
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
    repeat # probabilistic
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
#M  ModulusOfRcwaGroup( <G> ) . . . . . . . . . . . . . . . . for rcwa groups
##
InstallMethod( ModulusOfRcwaGroup,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> Modulus( G ) );

#############################################################################
##
#M  IsTame( <G> ) . . . . . . . . . . . . . . . . . . . . . . for rcwa groups
##
InstallMethod( IsTame,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> Modulus( G ) <> Zero( Source( One( G ) ) ) );

#############################################################################
##
#M  Multiplier( <G> ) . . . . . . . . . . . . . . . . . . . . for rcwa groups
##
InstallOtherMethod( Multiplier,
                    "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  R, orbs, thin, thick, quot, int;

    R := Source(One(G));
    if not IsTame(G) then return infinity; fi;
    orbs  := Orbits(G,RespectedPartition(G));
    thin  := List(orbs,o->First(o,cl->Density(cl)=Minimum(List(o,Density))));
    thick := List(orbs,o->First(o,cl->Density(cl)=Maximum(List(o,Density))));
    quot  := List([1..Length(orbs)],
                  i->Lcm(Mod(thin[i]),Mod(thick[i]))/Mod(thin[i])
                    *Lcm(Mod(thin[i]),Mod(thick[i]))/Mod(thick[i]));
    int   := List(quot,q->Length(AllResidues(R,q)));
    return quot[Position(int,Maximum(int))];
  end );

#############################################################################
##
#M  Divisor( <G> ) . . . . . . . . . . . . . . . . . . . . .  for rcwa groups
##
InstallOtherMethod( Divisor,
                    "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
                    Multiplier );

#############################################################################
##
#F  RespectedPartitionOfRcwaGroup  worker function: RespectedPartition[Short]
##
BindGlobal( "RespectedPartitionOfRcwaGroup",

  function ( G, short )

    local  R, P, m, moved, fixed, remaining, allcls, cls, cl, orb;

    if not IsTame(G) then return fail; fi;
    R         := Source(One(G));
    m         := Modulus(G);
    allcls    := AllResidueClassesModulo(R,m);
    cls       := allcls;
    moved     := Support(G);
    fixed     := Difference(R,moved);
    P         := AsUnionOfFewClasses(fixed);
    remaining := moved;
    while not IsEmpty(remaining) do
      cls := Filtered(cls, cl -> Intersection(cl,remaining) <> []);
      for cl in cls do
        orb := Orbit(G,cl);
        if short and Maximum(List(orb,Modulus)) <= m then break; fi;
        if not short and Minimum(List(orb,Modulus)) = m then break; fi;
      od;
      P         := Union(P,orb);
      remaining := Difference(remaining,Union(orb));
    od;
    Assert(1,Union(P)=R);
    Assert(2,Action(G,P)<>fail);
    return P;
  end );

#############################################################################
##
#M  RespectedPartitionShort( <G> ) . . . . . . . . . . . for tame rcwa groups
##
InstallMethod( RespectedPartitionShort,
               "for tame rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> RespectedPartitionOfRcwaGroup( G, true ) );

#############################################################################
##
#M  RespectedPartitionLong( <G> ) . . . . . . . . . . .  for tame rcwa groups
##
InstallMethod( RespectedPartitionLong,
               "for tame rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> RespectedPartitionOfRcwaGroup( G, false ) );

#############################################################################
##
#M  ActionOnRespectedPartition( <G> ) . . . . . . . . .  for tame rcwa groups
##
InstallMethod( ActionOnRespectedPartition,
               "for tame rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> Action( G, RespectedPartition( G ) ) );

#############################################################################
##
#M  RankOfKernelOfActionOnRespectedPartition( <G> ) . .  for tame rcwa groups
##
InstallMethod( RankOfKernelOfActionOnRespectedPartition,
               "for tame rcwa groups (RCWA)", true,
               [ IsRcwaGroup ], 0,

  function ( G )

    local  P, H, Pp, Hp, indices, bound, primes, prod, p;

    if IsTrivial(G) then return 0; fi;
    P     := RespectedPartition(G);
    H     := ActionOnRespectedPartition(G);
    bound :=   Modulus(G) * Size(H)
             * Maximum(List(GeneratorsOfGroup(G),
                            g->Maximum(List(Coefficients(g),
                                            c->AbsInt(c[2])))));
    if bound < 5 then bound := 5; fi;
    primes := []; p := 1; prod := 1;
    while prod <= bound do
      p    := NextPrimeInt(p); Add(primes,p);
      prod := prod * p;
    od;
    Pp := List(primes,p->Flat(List(P,cl->SplittedClass(cl,p))));
    Hp := List(Pp,P->Group(List(GeneratorsOfGroup(G),
                                gen->PermutationOpNC(gen,P,OnPoints))));
    indices := List(Hp,Size)/Size(H);
    SetKernelActionIndices(G,indices);
    SetRefinedRespectedPartitions(G,Pp);
    return Maximum(List([2..Length(primes)],
                        i->Number(Factors(indices[i]),p->p=primes[i])));
  end );

#############################################################################
##
#M  KernelOfActionOnRespectedPartition( <G> ) . . for tame rcwa groups over Z
##  
InstallMethod( KernelOfActionOnRespectedPartition,
               "for tame rcwa groups over Z (RCWA)", true,
               [ IsRcwaGroupOverZ ], 0,

  function ( G )

    local  P, KFullPoly, KPoly, genKFP, genKPoly, rank, K, H, g, h,
           k, kPoly, genG, genH, genK, cgspar, nrgens, crcs, i;

    P         := RespectedPartition(G);
    H         := ActionOnRespectedPartition(G);
    rank      := RankOfKernelOfActionOnRespectedPartition(G);
    genG      := GeneratorsOfGroup(G);
    genH      := GeneratorsOfGroup(H);
    genK      := [];
    KFullPoly := DirectProduct(List([1..Length(P)],i->DihedralPcpGroup(0)));
    genKFP    := GeneratorsOfGroup(KFullPoly);
    KPoly     := TrivialSubgroup(KFullPoly);
    K         := TrivialSubgroup(G);
    g         := genG[1];
    h         := genH[1];
    nrgens    := Length(genG);
    if Set(KernelActionIndices(G)) <> [1] then
      repeat
        k := g^Order(h);
        if not IsOne(k) then
          kPoly := One(KFullPoly);
          for i in [1..Length(P)] do
            for crcs in Factorization(RestrictedPerm(k,P[i])) do
              if IsClassReflection(crcs) then
                kPoly := kPoly*genKFP[2*i-1];
              elif not IsOne(crcs) then
                kPoly := kPoly*genKFP[2*i]^Determinant(crcs);
              fi;
            od;
          od;
          if not kPoly in KPoly then
            genKPoly := GeneratorsOfGroup(KPoly);
            genK     := GeneratorsOfGroup(K);
            if IsEmpty(genKPoly) then
              genKPoly := [kPoly];
              genK     := [k];
            else
              cgspar   := CgsParallel(genKPoly,genK);
              genKPoly := Concatenation(cgspar[1],[kPoly]);
              genK     := Concatenation(cgspar[2],[k]);
            fi;
            KPoly    := Subgroup(KFullPoly,genKPoly);
            K        := SubgroupNC(G,genK);
            if   ForAll([1..Length(RefinedRespectedPartitions(G))],
                        i->Size(Group(List(GeneratorsOfGroup(K),
                   gen->PermutationOpNC(gen,RefinedRespectedPartitions(G)[i],
                                            OnPoints))))
                 = KernelActionIndices(G)[i])
            then break; fi;
          fi;
        fi;
        i := Random([1..nrgens]);
        g := g * genG[i];
        h := h * genH[i];
      until false;
    fi;
    if not IsBound(genKPoly) then
      genKPoly := [One(KFullPoly)];
      genK     := [One(G)];
    else
      genKPoly := GeneratorsOfGroup(KPoly);
      genK     := GeneratorsOfGroup(K);
      cgspar   := CgsParallel(genKPoly,genK);
      genKPoly := cgspar[1];
      genK     := cgspar[2];
    fi;
    KPoly := Subgroup(KFullPoly,genKPoly);
    K     := SubgroupNC(G,genK);
    SetIndexInParent(K,Size(H));
    SetRespectedPartition(K,P);
    SetRankOfKernelOfActionOnRespectedPartition(K,rank);
    SetKernelOfActionOnRespectedPartition(K,K);
    if   not IsTrivial(K)
    then SetIsomorphismPcpGroup(K,EpimorphismByGeneratorsNC(K,KPoly));
    else SetIsomorphismPcpGroup(K,GroupHomomorphismByImages(K,KPoly,
                                  [One(K)],[One(KPoly)])); fi;
    return K;
  end );

#############################################################################
##
#M  RespectsPartition( <sigma>, <P> ) . . . . . . . .  for rcwa mappings of Z
##
InstallMethod( RespectsPartition,
               "for rcwa mappings of Z (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZ, IsList ], 0,

  function ( sigma, P )

    local  cl, c, c_rest, r, m, l;

    if   not ForAll(P,cl->IsUnionOfResidueClassesOfZ(cl) or IsIntegers(cl))
      or not ForAll(P,IsResidueClass)
      or not IsIntegers(Union(P)) or Sum(List(P,Density)) <> 1
    then TryNextMethod(); fi;
    if Permutation(sigma,P) = fail then return false; fi;
    c := Coefficients(sigma);
    for cl in P do
      r := Residues(cl)[1];
      m := Modulus(cl);
      l := Int(Modulus(sigma)/m);
      c_rest := c{[r+1,r+m+1..r+(l-1)*m+1]};
      if Length(Set(c_rest)) > 1 then return false; fi;
    od;
    return true;
  end );

#############################################################################
##
#M  RespectsPartition( <G>, <P> ) . . . . . . . . . . . . . . for rcwa groups
##
InstallMethod( RespectsPartition,
               "for rcwa groups (RCWA)",
               ReturnTrue, [ IsRcwaGroup, IsList ], 0,

  function ( G, P )
    return ForAll(GeneratorsOfGroup(G),g->RespectsPartition(g,P));
  end );

#############################################################################
##
#M  IsomorphismPermGroup( <G> ) . . . . . . . . for finite rcwa groups over Z
##
##  This method uses that the class reflection on a residue class r(m)
##  interchanges the residue classes r+m(3m) and r+2m(3m).
##
InstallMethod( IsomorphismPermGroup,
               "for finite rcwa groups (RCWA)",
               true, [ IsRcwaGroupOverZ ], 0,

  function ( G )

    local  P, P3, H, phi;

    if not IsFinite(G) then return fail; fi;
    P   := RespectedPartition(G);
    if   IsClassWiseOrderPreserving(G)
    then H := ActionOnRespectedPartition(G);
    else H := Action(G,Flat(List(P,cl->SplittedClass(cl,3)))); fi;
    phi := Immutable(EpimorphismByGeneratorsNC(G,H));
    if   not HasParent(G)
    then SetNiceMonomorphism(G,phi); SetNiceObject(G,H); fi;
    return phi;
  end );

#############################################################################
##
#M  IsomorphismMatrixGroup( <G> ) . . . . . . . . . . .  for tame rcwa groups
##
InstallMethod( IsomorphismMatrixGroup,
               "for tame rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  R, res, q, x, d, P, H, M, ModG, g, h, m, deg, r, b, c, pos, i, j;

    if not IsTame(G) then TryNextMethod(); fi;
    R := Source(One(G)); ModG := Modulus(G);
    if IsRcwaGroupOverGFqx(G) then
      q := Size(CoefficientsRing(R));
      x := IndeterminatesOfPolynomialRing(R)[1];
      res := [];
      for d in [1..DegreeOfLaurentPolynomial(ModG)] do
        res[d] := AllGFqPolynomialsModDegree(q,d,x);
      od;
    fi;
    g := GeneratorsOfGroup(G);
    P := RespectedPartitionShort(G);
    deg := 2 * Length(P);
    H := Action(G,P); h := GeneratorsOfGroup(H);
    m := [];
    for i in [1..Length(g)] do
      m[i] := MutableNullMat(deg,deg,R);
      for j in [1..deg/2] do
        b := [[0,0],[0,1]] * One(R);
        r := Residues(P[j])[1] mod Modulus(g[i]);
        if   IsRcwaGroupOverZOrZ_pi(G)
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
#M  NiceMonomorphism( <G> ) . . . . . . . . . . . . . .  for tame rcwa groups
##
InstallMethod( NiceMonomorphism,
               "for tame rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )
    if   IsTame(G)
    then if   IsTrivial(KernelOfActionOnRespectedPartition(G))
         then return IsomorphismPermGroup(G);
         else return IsomorphismMatrixGroup(G); fi;
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  NiceObject( <G> ) . . . . . . . . . . . . . . . . . . . . for rcwa groups
##
InstallMethod( NiceObject,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,
               G -> Image( NiceMonomorphism( G ) ) );

#############################################################################
##
#M  \in( <g>, <G> ) . . . . for an rcwa mapping of Z and an rcwa group over Z
##
##  If <G> is wild this may run into an infinite loop if <g> is not an
##  element of <G>.
##
InstallMethod( \in,
               "for an rcwa mapping of Z and an rcwa group over Z (RCWA)",
               ReturnTrue, [ IsRcwaMappingOfZ, IsRcwaGroupOverZ ], 0,

  function ( g, G )

    local  P, H, h, K, k, KPoly, KFullPoly, genKFP, kPoly, crcs,
           F, phi, gens, orbs, orbsmod, m, max, i;

    Info(InfoRCWA,2,"\\in for an rcwa mapping of Z ",
                    "and an rcwa group over Z");
    if not IsBijective(g)
    then Info(InfoRCWA,4,"<g> is not bijective."); return false; fi;
    gens := GeneratorsOfGroup(G);
    if IsOne(g) or g in gens or g^-1 in gens then
      Info(InfoRCWA,2,"<g> = 1 or one of <g> or <g>^-1 ",
                      "in generator list of <G>.");
      return true;
    fi;
    if not IsSubset(PrimeSet(G),PrimeSet(g)) then
      Info(InfoRCWA,2,"<g> and <G> have incompatible prime sets.");
      return false;
    fi;
    if not IsSubset(Factors(   Product(List(gens,Multiplier))
                             * Product(List(gens,Divisor))),
                    Filtered(Factors(Multiplier(g)*Divisor(g)),p->p<>1))
    then
      Info(InfoRCWA,2,"The multiplier or divisor of <g> has factors which");
      Info(InfoRCWA,2,"no multiplier or divisor of a generator of <G> has.");
      return false;
    fi;
    if        IsClassWiseOrderPreserving(G)
      and not IsClassWiseOrderPreserving(g) then
      Info(InfoRCWA,2,"<G> is class-wise order-preserving, <g> is not.");
      return false;
    fi;
    if Sign(g) = -1 and Set(gens,Sign) = [1] then
      Info(InfoRCWA,2,"Sign(<g>) is -1, but the sign of all generators ",
                      "of <G> is 1.");
      return false;
    fi;
    if Determinant(g) <> 0 and IsClassWiseOrderPreserving(G)
      and Set(gens,Determinant) = [0]
    then
      Info(InfoRCWA,2,"<G> lies in the kernel of the determinant ",
                      "epimorphism, but <g> does not.");
      return false;
    fi;
    if not IsSubset(Support(G),Support(g)) then
      Info(InfoRCWA,2,"Support(<g>) is not a subset of Support(<G>).");
      return false;
    fi;
    max := Maximum(Concatenation(List(Concatenation(gens,[g]),
                                      gen->Maximum(List(Coefficients(gen),
                                                        c->AbsInt(c[2])))),
                                 List(Concatenation(gens,[g]),Modulus)));
    if Minimum([0..max]^g) < 0 or Maximum([-max..-1]^g) >= 0 then
      if    ForAll(gens,gen->Minimum([0..max]^gen)>=0)
        and ForAll(gens,gen->Maximum([-max..-1]^gen)<0)
      then
        Info(InfoRCWA,2,"<G> fixes the nonnegative integers setwisely,");
        Info(InfoRCWA,2,"but <g> does not.");
        return false;
      fi;
    fi;
    if not IsTame(G) then
      orbs := ShortOrbits(G,Intersection(Support(G),[-100..100]),50);
      if orbs <> [] then
        if ForAny(orbs,orb->Permutation(g,orb)=fail) then
          Info(InfoRCWA,2,"<g> does not act on some finite orbit of <G>.");
          return false;
        fi;
        if ForAny(orbs,orb->not Permutation(g,orb) in Action(G,orb)) then
          Info(InfoRCWA,2,"<g> induces a permutation on some finite orbit");
          Info(InfoRCWA,2,"of <G> which does not lie in the group induced");
          Info(InfoRCWA,2,"by <G> on this orbit.");
          return false;
        fi;
      fi;
      m       := Lcm(List(Concatenation(gens,[g]),Modulus));
      orbsmod := List(Projections(G,m),proj->Support(Image(proj)));
      if ForAny(orbsmod,orb->orb^g<>orb) then
        Info(InfoRCWA,2,"<g> does not leave the partition of Z into unions");
        Info(InfoRCWA,2,"of residue classes (mod ",m,") invariant which is");
        Info(InfoRCWA,2,"fixed by <G>.");
        return false;
      fi;
      Info(InfoRCWA,2,"<G> is wild -- trying to factor <g> into gen's ...");
      phi := EpimorphismFromFreeGroup(G);
      return PreImagesRepresentative(phi,g) <> fail;
    else
      if Modulus(G) mod Modulus(g) <> 0 then
        Info(InfoRCWA,2,"Mod(<g>) does not divide Mod(<G>).");
        return false;
      fi;
      if not IsTame(g) then
        Info(InfoRCWA,2,"<G> is tame, but <g> is wild.");
        return false;
      fi;
      if IsFinite(G) and Order(g) = infinity then
        Info(InfoRCWA,2,"<G> is finite, but <g> has infinite order.");
        return false;
      fi;
      P := RespectedPartition(G);
      H := ActionOnRespectedPartition(G);
      h := Permutation(g,P);
      if h = fail then
        Info(InfoRCWA,2,"<g> does not act on RespectedPartition(<G>).");
        return false;
      fi;
      if not RespectsPartition(g,P) then
        Info(InfoRCWA,2,"<g> does not respect RespectedPartition(<G>).");
        return false;
      fi;
      if not h in H then
        Info(InfoRCWA,2,"The permutation induced by <g> on ",
                        "P := RespectedPartition(<G>)");
        Info(InfoRCWA,2,"is not an element of the permutation group ",
                        "which is induced by <G> on P.");
        return false;
      fi;

      Info(InfoRCWA,2,"Computing an element of <G> which acts like <g>");
      Info(InfoRCWA,2,"on RespectedPartition(<G>).");

      phi := EpimorphismFromFreeGroup(H);
      h   := PreImagesRepresentative(phi,h:NoStabChain);
      if h = fail then return false; fi;
      h   := Product(List(LetterRepAssocWord(h),
                          id->gens[AbsInt(id)]^SignInt(id)));
      k   := g/h;

      Info(InfoRCWA,2,"Checking membership of the quotient in the kernel ");
      Info(InfoRCWA,2,"of the action of <g> on RespectedPartition(<G>).");

      K         := KernelOfActionOnRespectedPartition(G);
      KPoly     := Range(IsomorphismPcpGroup(K));
      KFullPoly := Parent(KPoly);
      genKFP    := GeneratorsOfGroup(KFullPoly);
      kPoly     := One(KFullPoly);
      for i in [1..Length(P)] do
        for crcs in Factorization(RestrictedPerm(k,P[i])) do
          if IsClassReflection(crcs) then
            kPoly := kPoly*genKFP[2*i-1];
          elif not IsOne(crcs) then
            kPoly := kPoly*genKFP[2*i]^Determinant(crcs);
          fi;
        od;
      od;
      return kPoly in KPoly;
    fi;
  end );

#############################################################################
##
#M  \in( <g>, <G> ) . . . . . . . . . . for an rcwa mapping and an rcwa group
##
##  This may run into an infinite loop if <G> is infinite and <g> is not an
##  element of <G>.
##
InstallMethod( \in,
               "for an rcwa mapping and an rcwa group (RCWA)",
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
#M  Size( <G> ) . . . . . . . . . . . . . . . . . . .  for rcwa groups over Z
##
##  This method checks whether <G> is tame and the kernel of the action of
##  <G> on a respected partition has rank 0 -- if so, it returns the
##  size of the permutation group induced on this partition, and if not it
##  returns infinity.
##
InstallMethod( Size,
               Concatenation("for rcwa groups over Z, use action on ",
                             "respected partition (RCWA)"),
               true, [ IsRcwaGroupOverZ ], 0,

  function ( G )

    local  orbs, orbs_old, gens, g, maxpts;

    # A few `trivial' checks.

    if IsTrivial(G) then return 1; fi;
    if ForAny(GeneratorsOfGroup(G),g->Order(g)=infinity)
    then return infinity; fi;
    if not IsTame(G) then return infinity; fi;

    # On the one hand, an orbit of a finite tame group <G> can intersect
    # in at most 1 resp. 2 points with any residue class in a respected
    # partition, depending on whether <G> is class-wise order-preserving
    # or not. On the other if <G> is infinite, one of its orbits contains
    # an entire residue class from the respected partition.

    orbs := List(RespectedPartition(G),cl->[Representative(cl)]);
    if IsClassWiseOrderPreserving(G) then maxpts := 1; else
      orbs   := Concatenation(orbs,orbs+List(RespectedPartition(G),
                                             cl->[Modulus(cl)]));
      maxpts := 2;
    fi;
    gens := GeneratorsAndInverses(G);
    repeat
      orbs_old := List(orbs,ShallowCopy);
      for g in gens do orbs := List(orbs,orb->Union(orb,orb^g)); od;
    until orbs = orbs_old
       or ForAny(orbs,orb->ForAny(RespectedPartition(G),
                                  cl->Length(Intersection(cl,orb))>maxpts));

    if orbs = orbs_old then return Size(Action(G,Union(orbs)));
                       else return infinity; fi;
  end );

#############################################################################
##
#M  Size( <G> ) . . . . . . . . . . . . . . . . . . . . . . . for rcwa groups
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
#M  IntegralizingConjugator( <G> ) . . . . . . .  for tame rcwa groups over Z
##
InstallOtherMethod( IntegralizingConjugator,
                    "for tame rcwa groups over Z (RCWA)", true,
                    [ IsRcwaGroupOverZ ], 0,

  function ( G )

    local  P;

    if IsIntegral(G) then return One(G); fi;
    P := RespectedPartition(G); if P = fail then return fail; fi;
    return RepresentativeAction(RCWA(Integers),P,
                                AllResidueClassesModulo(Integers,Length(P)));
  end );

#############################################################################
##
#M  IntegralConjugate( <G> ) . . . . . . . . . . . . . . for tame rcwa groups
##
InstallOtherMethod( IntegralConjugate,
                    "for tame rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )

    local  result, R, m;

    result := G^IntegralizingConjugator(G);
    R      := Source(One(result));
    m      := Lcm(List(GeneratorsOfGroup(result),Modulus));
    SetRespectedPartition(result,AllResidueClassesModulo(R,m));
    return result;
  end );

#############################################################################
##
#M  IntegralizingConjugator( <sigma> ) . . . . .  for tame bij. rcwa mappings
##
InstallMethod( IntegralizingConjugator,
               "for tame bijective rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 0,
               sigma -> IntegralizingConjugator( Group( sigma ) ) );

#############################################################################
##
#M  IntegralConjugate( <sigma> ) . . . . . . . .  for tame bij. rcwa mappings
##
InstallMethod( IntegralConjugate,
               "for tame bijective rcwa mappings (RCWA)", true,
               [ IsRcwaMapping ], 0,

  function ( sigma )

    local  result, R, m;

    result := sigma^IntegralizingConjugator(sigma);
    R      := Source(result);
    m      := Modulus(result);
    SetRespectedPartition(result,AllResidueClassesModulo(R,m));
    return result;
  end );

#############################################################################
##
#M  StandardizingConjugator( <sigma> )  for tame bijective rcwa mappings of Z
##
InstallMethod( StandardizingConjugator,
               "for tame bijective rcwa mappings of Z (RCWA)", true,
               [ IsRcwaMappingOfZ ], 0,

  function ( sigma )

    local  toint, int, m, mtilde, mTilde, P, r, rtilde, c, cycs, lngs,
           cohorts, cohort, l, nrcycs, res, cyc, n, ntilde, i, j, k;

    if not IsBijective(sigma) or not IsTame(sigma) then TryNextMethod(); fi;
    toint   := IntegralizingConjugator(sigma);
    int     := IntegralConjugate(sigma);
    m       := Modulus(int);
    P       := AllResidueClassesModulo(Integers,m);
    cycs    := Cycles(int,P);
    lngs    := Set(List(cycs,Length));
    cohorts := List(lngs,l->Filtered(cycs,cyc->Length(cyc)=l));
    mtilde  := Sum(lngs);
    c       := List([1..m],i->[1,0,1]);
    rtilde  := 0;
    for cohort in cohorts do
      nrcycs := Length(cohort);
      l      := Length(cohort[1]);
      res    := List([1..l],i->List([1..nrcycs],
                                    j->Residues(cohort[j][i])[1]));
      cyc    := List([1..nrcycs],j->Cycle(int,res[1][j]));
      mTilde := nrcycs * mtilde;
      for i in [1..l] do
        for r in res[i] do
          j      := Position(res[i],r);
          n      := cyc[j][i];
          ntilde := (j-1)*mtilde+rtilde;
          k      := (ntilde*m-mTilde*n-m*rtilde+mtilde*r)/(m*mtilde);
          c[r+1] := [mTilde,k*m*mtilde+m*rtilde-mtilde*r,m];
        od;
        rtilde := rtilde + 1;
      od;
    od; 
    return toint * RcwaMapping(c);
  end );

#############################################################################
##
#M  StandardConjugate( <f> ) . . . . . . . . . . . . . for tame rcwa mappings
##
InstallMethod( StandardConjugate,
               "for tame rcwa mappings (RCWA)", true, [ IsRcwaMapping ], 0,
               f -> f^StandardizingConjugator( f ) );

#############################################################################
##
#M  IsConjugate( RCWA( Integers ), <f>, <g> ) 
##
##  For rcwa mappings of $\Z$, in the full group `RCWA( Integers )'.
##  Checks whether the standard conjugates of <f> and <g> are equal, if the
##  mappings are tame, and looks for different lengths of short cycles
##  otherwise (the latter will not terminate if <f> and <g> are conjugate).
##
InstallOtherMethod( IsConjugate,
                    "for two rcwa mappings of Z, in RCWA(Z) (RCWA)",
                    true, [ IsNaturalRCWA_Z, IsRcwaMappingOfZ,
                            IsRcwaMappingOfZ ], 0,

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
##  For rcwa mappings of $\Z_{\pi}$, in `RCWA( Z_pi( <pi> ) )'.
##  Only trivial checks are done. The method cannot find a positive result
##  unless <f> and <g> are equal.
##
InstallOtherMethod( IsConjugate,
                    Concatenation("for two rcwa mappings of Z_(pi) ",
                                  "in RCWA(Z_(pi)) (RCWA)"),
                    ReturnTrue, 
                    [ IsNaturalRCWA_Z_pi,
                      IsRcwaMappingOfZ_pi, IsRcwaMappingOfZ_pi ], 0,

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
##  For tame rcwa mappings of $\Z$ under the conjugation action in the full
##  group `RCWA( Integers )'. The method returns an rcwa mapping <h> such
##  that <f>^<h> = <g>, in case such a mapping exists and fail otherwise.
##  The action <act> must be `OnPoints'.
##
InstallOtherMethod( RepresentativeActionOp,
                    "for RCWA(Z) and two tame rcwa mappings of Z (RCWA)",
                    true,
                    [ IsNaturalRCWA_Z, IsRcwaMappingOfZ, IsRcwaMappingOfZ,
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
#M  RepresentativeActionOp( RCWA( Integers ), <f>, <g>, <act> ) 
##
##  Special method for products of the same numbers of class shifts, inverses
##  of class shifts, class reflections and class transpositions, each, whose
##  supports are pairwise disjoint and do not entirely cover Z up to a finite
##  complement.
##
InstallOtherMethod( RepresentativeActionOp,
                    "for RCWA(Z) and products of disjoint CS/CR/CT (RCWA)",
                    true,
                    [ IsNaturalRCWA_Z, IsRcwaMappingOfZ, IsRcwaMappingOfZ,
                      IsFunction ], 100,

  function ( RCWA_Z, f, g, act )

    local  RefinedPartition, Sorted, maps, facts, P, l, sigma, i;

    RefinedPartition := function ( P, k )

      local  l, mods, min, pos;

      P := ShallowCopy(P); l := Length(P);
      while l < k do
        mods   := List(P,Modulus);
        min    := Minimum(mods);
        pos    := Position(mods,min);
        P[pos] := SplittedClass(P[pos],2);
        P      := Flat(P);
        l      := l + 1;
      od;
      return P;
    end;

    Sorted := l -> [Filtered(l,fact->IsClassShift(fact)
                                  or IsClassShift(fact^-1)),
                    Filtered(l,IsClassReflection),
                    Filtered(l,IsClassTransposition)];              

    if act <> OnPoints then TryNextMethod(); fi;
    if f = g then return One(f); fi;
    if not ForAll([f,g],IsTame) then TryNextMethod(); fi;
    if Order(f) <> Order(g) then return fail; fi;
    maps  := [f,g];
    facts := List(maps,FactorizationIntoCSCRCT);
    if   Length(facts[1]) <> Length(facts[2])
      or 1 in List(maps,map->Density(Support(map)))
      or ForAny([1..2],i->Density(Support(maps[i]))
                       <> Sum(List(facts[i],fact->Density(Support(fact)))))
      or not ForAll(Union(facts),
                    fact ->   IsClassShift(fact) or IsClassShift(fact^-1)
                           or IsClassReflection(fact)
                           or IsClassTransposition(fact))
    then TryNextMethod(); fi;
    facts := List(facts,Sorted);
    if   List(facts[1],Length) <> List(facts[2],Length)
    then TryNextMethod(); fi;
    P := List(maps,
              map->AsUnionOfFewClasses(Difference(Integers,Support(map))));
    l  := Maximum(List(P,Length));
    for i in [1..2] do
      if l > Length(P[i]) then P[i] := RefinedPartition(P[i],l); fi;
    od;
    for i in [1..2] do
      Append(P[i],Flat(List(Flat(facts[i]),
                  fact->Filtered(LargestSourcesOfAffineMappings(fact),
                                 cl->Intersection(Support(fact),cl)<>[]))));
    od;
    sigma := RcwaMapping(P[1],P[2]);
    for i in [1..Length(facts[1][1])] do
      if   Number([facts[1][1][i]^-1,facts[2][1][i]^-1],IsClassShift) = 1
      then sigma := ClassReflection(Support(facts[1][1][i])) * sigma; fi;
    od;
    if f^sigma <> g then Error("`RepresentativeAction' failed.\n"); fi;
    return sigma;
  end );

#############################################################################
##
#M  RepresentativeActionOp( RCWA( Integers ), <ct1>, <ct2>, <act> ) 
##
##  Special method for two class transpositions which are both not equal to
##  n -> n + (-1)^n. The factorization of the result into 6 class transposi-
##  tions is stored. The existence of such products is used in the proof that
##  the group which is generated by all class transpositions is simple.
##
InstallOtherMethod( RepresentativeActionOp,
                    "for RCWA(Z) and two class transpositions (RCWA)",
                    true,
                    [ IsNaturalRCWA_Z, IsRcwaMappingOfZ, IsRcwaMappingOfZ,
                      IsFunction ], 200,

  function ( RCWA_Z, ct1, ct2, act )

    local  result, sixcts, cls, D, supd;

    if act <> OnPoints or not ForAll([ct1,ct2],IsClassTransposition)
      or ClassTransposition(0,2,1,2) in [ct1,ct2]
    then TryNextMethod(); fi;
    cls  := Concatenation(List([ct1,ct2],TransposedClasses));
    supd := 1 - Sum(List(cls{[3,4]},Density));
    D := AsUnionOfFewClasses(Difference(Integers,Union(cls{[1,2]})))[1];
    D := SplittedClass(D,Int(Density(D)/supd)+1)[1];
    Append(cls,SplittedClass(D,2));
    D := AsUnionOfFewClasses(Difference(Integers,Union(cls{[3..6]})));
    if Length(D) = 1 then D := SplittedClass(D[1],2); fi;
    Append(cls,D{[1,2]});
    sixcts := List([cls{[1,5]},cls{[2,6]},cls{[5,7]},
                    cls{[6,8]},cls{[3,7]},cls{[4,8]}],ClassTransposition);
    result := Product(sixcts);
    SetFactorizationIntoCSCRCT(result,sixcts);
    return result;
  end );

#############################################################################
##
#M  RepresentativeActionOp( RCWA(Integers), <n1>, <n2>, <act> )
##
InstallOtherMethod( RepresentativeActionOp,
                    "for RCWA(Z) and two integers (RCWA)", ReturnTrue,
                    [ IsNaturalRCWA_Z, IsInt, IsInt, IsFunction ], 0,

  function ( RCWA_Z, n1, n2, act )
    if act <> OnPoints then TryNextMethod(); fi;
    return ClassShift(0,1)^(n2-n1);
  end );

#############################################################################
##
#M  RepresentativeActionOp( RCWA(Integers), <l1>, <l2>, <act> )
##
InstallOtherMethod( RepresentativeActionOp,
                    "for RCWA(Z) and two k-tuples of integers (RCWA)",
                    ReturnTrue,
                    [ IsNaturalRCWA_Z, IsList, IsList, IsFunction ], 0,

  function ( RCWA_Z, l1, l2, act )

    local  g, range, perm, exp, points, n;

    points := Union(l1,l2);
    if not IsSubset(Integers,points) then return fail; fi;
    range := [1..Maximum(points)-Minimum(points)+1]; n := Length(range);
    exp := -Minimum(points)+1;
    perm := RepresentativeAction(SymmetricGroup(n),l1+exp,l2+exp,act);
    if perm = fail then return fail; fi;
    g := RcwaMapping(perm,range);
    return g^(ClassShift(0,1)^-exp);
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
##  An rcwa mapping <g> which maps the partition <P1> to the partition <P2>
##  and is
##
##  - affine on the elements of <P1>, if the option `IsTame' is not set
##    and all elements of both partitions <P1> and <P2> are single residue
##    classes, and
##
##  - tame, if the option `IsTame' is set.
##
##  The arguments <P1> and <P2> must be partitions of $\Z$ into equally many
##  disjoint residue class unions, and the argument <act> is ignored.
##
InstallOtherMethod( RepresentativeActionOp,
                    "for RCWA(Z) and two class partitions (RCWA)", true,
                    [ IsNaturalRCWA_Z, IsList, IsList, IsFunction ], 0,

  function ( RCWA_Z, P1, P2, act )

    local  SplitClass, g, tame, m, c, P, min, minpos, Phat, Buckets, b,
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

    if   Length(P1) <> Length(P2)
      or not ForAll(P1,IsUnionOfResidueClassesOfZ)
      or not ForAll(P2,IsUnionOfResidueClassesOfZ)
      or [Union(List(P1,IncludedElements)),Union(List(P1,ExcludedElements)),
          Union(List(P2,IncludedElements)),Union(List(P2,ExcludedElements))]
         <> [[],[],[],[]]
      or Sum(List(P1,Density)) <> 1 or Sum(List(P2,Density)) <> 1
      or Union(P1) <> Integers or Union(P2) <> Integers
    then TryNextMethod(); fi;

    if not ForAll(P1,IsResidueClass) or not ForAll(P2,IsResidueClass) then
      P1 := List(P1,AsUnionOfFewClasses);
      P2 := List(P2,AsUnionOfFewClasses);
      P  := [P1,P2];
      for j in [1..Length(P1)] do
        if Length(P[1][j]) <> Length(P[2][j]) then
          if Length(P[1][j]) < Length(P[2][j]) then i := 1; else i := 2; fi;
          repeat
            min    := Minimum(List(P[i][j],Modulus));
            minpos := Position(List(P[i][j],Modulus),min);
            P[i][j][minpos] := SplittedClass(P[i][j][minpos],2);
            P[i][j] := Flat(P[i][j]);
          until Length(P[1][j]) = Length(P[2][j]);
        fi;
      od;
      P1 := Flat(P[1]); P2 := Flat(P[2]);
    fi;

    if ValueOption("IsTame") <> true then
      g := RcwaMapping(P1,P2);
    else
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
#M  Ball( <G>, <g>, <d> ) . . . . . . . .  for a group and an element thereof
##
##  As element tests can be expensive, this method does not check whether
##  <g> is indeed an element of <G>.
##
InstallMethod( Ball,
               "for a group and an element thereof (RCWA)", ReturnTrue,
               [ IsGroup, IsMultiplicativeElement, IsPosInt ], 0,

  function ( G, g, d )

    local  ball, gens, k;

    if not IsCollsElms(FamilyObj(G),FamilyObj(g)) then TryNextMethod(); fi;
    ball := [g];
    gens := Set(GeneratorsAndInverses(G));
    for k in [1..d] do
      ball := Union(ball,Union(List(gens,gen->ball*gen)));
    od;
    return ball;
  end );

#############################################################################
##
#M  Ball( <G>, <g>, <d> ) . . . . . . . . for a permutation group and a point
##
InstallOtherMethod( Ball,
                    "for a permutation group and a point (RCWA)", ReturnTrue,
                    [ IsGroup, IsObject, IsPosInt, IsFunction ], 0,

  function ( G, p, d, act )

    local  ball, gens, k;

    ball := [p];
    gens := Set(GeneratorsAndInverses(G));
    for k in [1..d] do
      ball := Union(ball,Union(List(gens,gen->List(ball,pt->act(pt,gen)))));
    od;
    return ball;
  end );

#############################################################################
## 
#M  OrbitUnion( <G>, <S> ) . . . . . . . . . . .  for an rcwa group and a set
##
##  This method might run into an infinite loop.
## 
InstallMethod( OrbitUnion,
               "for an rcwa group and a set (RCWA)", ReturnTrue,
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
#M  IsTransitive( <G>, <S> ) . .  for an rcwa group and a residue class union
##
##  This method might fail or run into an infinite loop.
##
InstallOtherMethod( IsTransitive,
                    "for an rcwa group and a residue class union (RCWA)",
                    ReturnTrue, [ IsRcwaGroup, IsListOrCollection ], 0,

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
    if   (IsRcwaGroupOverGFqx(G) or IsZ_pi(R))
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
    if   (IsRcwaGroupOverGFqx(G) or IsZ_pi(R))
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
#M  Transitivity( <G>, Integers ) . . . . . .  for an rcwa group over Z and Z
#M  Transitivity( <G>, NonnegativeIntegers )
#M  Transitivity( <G>, PositiveIntegers )
##
##  This method might fail or run into an infinite loop.
##
InstallOtherMethod( Transitivity,
                    "for an rcwa group over Z and one of Z, N_0 or N (RCWA)",
                    ReturnTrue, [ IsRcwaGroupOverZ, IsCollection ], 0,

  function ( G, D )

    local  gens, g, tups, tup, tupslng, invpairs, max, dom, finorb,
           stab, stabelm, decs, dec, decsp, decsm, bound, trs,
           S0, S, S_old, old_S, maxind, orb, oldorb, k, l, l0, m, str, i, j;

    if not (   IsIntegers(D) or IsNonnegativeIntegers(D)
            or IsPositiveIntegers(D))
    then TryNextMethod(); fi;

    if ValueOption("RCWADevel") <> true then
      Info(InfoWarning,1,
        "`Transitivity' for rcwa groups is not yet supported.");
      Info(InfoWarning,1,
        "If you want to try experimental code, set the option `RCWADevel'");
      Info(InfoWarning,1,
        "and set the info level of `InfoRCWA' at least equal to 2.");
      TryNextMethod();
    fi;

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
#M  IsPrimitive( <G>, <S> ) . . . for an rcwa group and a residue class union
##
##  This method might fail or run into an infinite loop.
##
InstallOtherMethod( IsPrimitive,
                    "for an rcwa group and a residue class union (RCWA)",
                    ReturnTrue, [ IsRcwaGroupOverZ,
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
                    "for tame rcwa groups over Z (RCWA)", ReturnTrue,
                    [ IsRcwaGroupOverZ, IsInt, IsList, IsList, IsFunction ],
                    0,

  function ( G, pnt, gens, acts, act )

    local  P, K, where, gensrests, noncwoppos, m, S, orb, i;

    if act <> OnPoints then TryNextMethod(); fi;
    orb := ShortOrbits(G,[pnt],100);
    if orb <> [] then return orb[1]; fi;
    if IsFinite(G) or not IsTame(G) then TryNextMethod(); fi;
    P          := RespectedPartition(G);
    K          := KernelOfActionOnRespectedPartition(G);
    where      := First(P,cl->pnt in cl);
    gensrests  := List(GeneratorsOfGroup(K),g->RestrictedPerm(g,where));
    noncwoppos := Filtered([1..Length(gensrests)],
                           i->not IsClassWiseOrderPreserving(gensrests[i]));
    for i in noncwoppos{[2..Length(noncwoppos)]} do
      gensrests[i] := gensrests[i] * gensrests[noncwoppos[1]];
    od;
    m :=   Gcd(List(Filtered(gensrests,IsClassWiseOrderPreserving),
                    Determinant))
         * Modulus(where);
    S := ResidueClass(Integers,m,pnt);
    S := Union(S,S^gensrests[noncwoppos[1]]);
    return OrbitUnion(G,S);
  end );

#############################################################################
##
#M  ViewObj( <RG> ) . . . . . . . . . . . . .  for group rings of rcwa groups
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
#M  EpimorphismFromFreeGroup( <G> ) . . . . . . . . . . . . . for rcwa groups
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
               "for hom's from free groups to rcwa groups over Z (RCWA)",
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
      or not (IsRcwaGroupOverZ(G) or IsPermGroup(G))
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
InstallMethod( Factorization,
               "for rcwa mappings in rcwa groups (RCWA)", true,
               [ IsRcwaGroup, IsRcwaMapping ], 0,

  function ( G, g )
    return PreImagesRepresentative(EpimorphismFromFreeGroup(G),g);
  end );

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
#M  IsPerfect( <G> ) . . . . . . . . . . . . . . . . . for rcwa groups over Z
##
InstallMethod( IsPerfect,
               "for rcwa groups over Z (RCWA)", ReturnTrue,
               [ IsRcwaGroupOverZ ], 0,

  function ( G )

    local  H;

    if IsTrivial(G) then return true; fi;
    if IsAbelian(G) then return false; fi;
    if IsRcwaGroupOverZ(G) then
      if   ForAny(GeneratorsOfGroup(G),g->Sign(g)<>1)
        or (     IsClassWiseOrderPreserving(G)
             and ForAny(GeneratorsOfGroup(G),g->Determinant(g)<>0))
      then return false; fi;
    fi;
    if not IsTame(G) then TryNextMethod(); fi;
    H := ActionOnRespectedPartition(G);
    if   IsTransitive(H,[1..LargestMovedPoint(H)])
    then return IsPerfect(H); else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  IsSimpleGroup( <G> ) . . . . . . . . . . . . . . . for rcwa groups over Z
##
InstallMethod( IsSimpleGroup,
               "for rcwa groups over Z (RCWA)", ReturnTrue,
               [ IsRcwaGroupOverZ ], 0,

  function ( G )
    if not IsTame(G) and not IsPerfect(G) then return false; fi;
    if IsTame(G) and not IsFinite(G) then return false; fi;
    if   IsFinite(G)
    then return IsSimpleGroup(Image(IsomorphismPermGroup(G))); fi;
    TryNextMethod();
  end );

#############################################################################
##
#M  NaturalHomomorphismByNormalSubgroupNCOrig( <G>, <N> ) . . for rcwa groups
##
InstallMethod( NaturalHomomorphismByNormalSubgroupNCOrig,
               "for rcwa groups, requiring finite index (RCWA)", ReturnTrue,
               [ IsRcwaGroup, IsRcwaGroup ], 0,

  function ( G, N )

    local  cosets, img;

    if not IsNormal(G,N) then return fail; fi;
    if IndexNC(G,N) = infinity then TryNextMethod(); fi;
    cosets := RightCosets(G,N);
    img    := Action(G,cosets,OnRight);
    return EpimorphismByGeneratorsNC(G,img);
  end );

#############################################################################
##
#M  IndexNC( <G>, <H> ) . . . . . . . . . . . . . . . . . . . for rcwa groups
##
InstallMethod( IndexNC,
               "for rcwa groups (RCWA)", ReturnTrue,
               [ IsRcwaGroup, IsRcwaGroup ], 0,

  function ( G, H )
    if IsClassWiseOrderPreserving(G)
      and Set(List(GeneratorsOfGroup(G),Determinant)) <> [0]
      and Set(List(GeneratorsOfGroup(H),Determinant)) =  [0]
    then return infinity; fi;
    if IsTame(H) and not IsTame(G) then return infinity; fi;
    if IsTame(G) and RankOfKernelOfActionOnRespectedPartition(G)
                   > RankOfKernelOfActionOnRespectedPartition(H)
    then return infinity; fi;
    return Length(RightCosets(G,H));
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
                    "for rcwa groups (RCWA)", ReturnTrue,
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
#M  Induction( <G>, <f> ) . . . . . . . . . . . . . . . . . . for rcwa groups
##
InstallOtherMethod( Induction,
                    "for rcwa groups (RCWA)", ReturnTrue,
                    [ IsRcwaGroup, IsRcwaMapping ], 0,

  function ( G, f )

    local Gf;

    if Source(One(G)) <> Source(f) or not IsInjective(f)
      or not IsSubset(Image(f),MovedPoints(G))
    then return fail; fi;

    Gf := GroupByGenerators(List(GeneratorsOfGroup(G),g->Induction(g,f)));

    if HasIsTame(G) then SetIsTame(Gf,IsTame(G)); fi;
    if HasSize(G)   then SetSize(Gf,Size(G)); fi;

    return Gf;
  end );

#############################################################################
##
#M  DirectProductOp( <groups>, <onegroup> ) . . . . .  for rcwa groups over Z
##
InstallMethod( DirectProductOp,
               "for rcwa groups over Z (RCWA)", ReturnTrue,
               [ IsList, IsRcwaGroupOverZ ], 0,

  function ( groups, onegroup )

    local  D, factors, f, m, G, gens, info, first;

    if   IsEmpty(groups) or not ForAll(groups,IsRcwaGroupOverZ)
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
    if   ForAny(groups,grp->HasSize(grp) and not IsFinite(grp))
    then SetSize(D,infinity); fi;
    if   ForAll(groups,grp->HasSize(grp) and IsInt(Size(grp)))
    then SetSize(D,Product(List(groups,Size))); fi;

    return D;
  end );

#############################################################################
##
#M  WreathProduct( <G>, <P> ) .  for rcwa group over Z and finite perm.-group
##
InstallMethod( WreathProduct,
               "for an rcwa group over Z and a finite perm.-group (RCWA)",
               ReturnTrue, [ IsRcwaGroupOverZ, IsPermGroup ], 0,

  function ( G, P )

    local  prod, info, m, orbreps, blocks, base, h, nrgensG;

    nrgensG := Length(GeneratorsOfGroup(G));
    m       := DegreeAction(P);
    orbreps := List(Orbits(P,MovedPoints(P)),Representative);
    blocks  := AllResidueClassesModulo(m);
    base    := DirectProduct(List([0..m-1],r->G));
    h       := RcwaGroupByPermGroup(P);
    prod    := Group(Concatenation(GeneratorsOfGroup(base),
                                   GeneratorsOfGroup(h)));
    info    := rec( groups := [ G, P ], alpha := IdentityMapping(P),
                    base := base, basegens := GeneratorsOfGroup(base),
                    I := P, degI := m, hgens := GeneratorsOfGroup(h),
                    components := blocks,
                    embeddings := [ GroupHomomorphismByImagesNC( G, prod,
                                      GeneratorsOfGroup(G),
                                      ~.basegens{[1..nrgensG]} ),
                                    GroupHomomorphismByImagesNC( P, prod,
                                      GeneratorsOfGroup(P), ~.hgens ) ] );
    SetWreathProductInfo(prod,info);
    if HasIsTame(G) then
      if IsTame(G) then
        SetIsTame(prod,true);
        if HasRespectedPartition(G) then
          SetRespectedPartition(prod,Union(List([0..m-1],
                                     r->m*RespectedPartition(G)+r)));
        fi;
      else SetIsTame(prod,false); fi;
    fi;
    if HasSize(G) then
      if IsFinite(G) then SetSize(prod,Size(G)^m*Size(P));
                     else SetSize(prod,infinity); fi;
    fi;
    return prod;
  end );

#############################################################################
##
#M  WreathProduct( <G>, <Z> ) . . . . . .  for an rcwa group over Z and (Z,+)
##
InstallMethod( WreathProduct,
               "for an rcwa group over Z and an infinite cyclic gp. (RCWA)",
               ReturnTrue, [ IsRcwaGroupOverZ, IsGroup and IsCyclic ], 0,

  function ( G, Z )

    local  prod, info, Gpi, z;

    if   Length(GeneratorsOfGroup(Z)) <> 1 or IsFinite(Z)
    then TryNextMethod(); fi;
    Gpi := Restriction(G,RcwaMapping([[4,3,1]]));
    z   := ClassTransposition(0,2,1,2) * ClassTransposition(0,2,1,4);
    SetIsTame(z,false); SetOrder(z,infinity);
    prod := Group(Concatenation(GeneratorsOfGroup(Gpi),[z]));
    info := rec( groups := [ G, Z ], alpha := IdentityMapping(Z),
                 I := Z, degI := infinity, hgens := [ z ],
                 embeddings := [ GroupHomomorphismByImagesNC( G, prod,
                                   GeneratorsOfGroup(G),
                                   GeneratorsOfGroup(Gpi)),
                                 GroupHomomorphismByImagesNC( Z, prod,
                                   GeneratorsOfGroup(Z), [z] ) ] );
    SetWreathProductInfo(prod,info);
    SetIsTame(prod,false); SetSize(prod,infinity);
    return prod;
  end );

#############################################################################
##
#M  Embedding( <W>, <i> ) . . . . . . . . . . for a wreath product and 1 or 2
##
InstallMethod( Embedding,
               "for a wreath product and 1 or 2 (RCWA)",
               ReturnTrue, [ HasWreathProductInfo, IsPosInt ], 0,

  function ( W, i )
    if not i in [1,2] then TryNextMethod(); fi;
    return WreathProductInfo(W).embeddings[i];
  end );

#############################################################################
##
#M  IsomorphismRcwaGroupOverZ( <F> ) . . . . . . . . . . . .  for free groups
#M  IsomorphismRcwaGroup( <F> )
##
##  This method uses an adaptation of the construction given on page 27
##  of the book Pierre de la Harpe: Topics in Geometric Group Theory from
##  PSL(2,C) to RCWA(Z).
##
InstallMethod( IsomorphismRcwaGroupOverZ,
               "for free groups (RCWA)", true, [ IsFreeGroup ], 0,

  function ( F )

    local  rank, m, D, gamma, RCWA_Z, phi, image, i;

    rank := Length(GeneratorsOfGroup(F));
    if rank = 1 then
      phi := GroupHomomorphismByImagesNC(F,Group(ClassShift(0,1)),
                                         [F.1],[ClassShift(0,1)]);
      SetSize(Image(phi),infinity); SetIsTame(Image(phi),true);
      SetIsBijective(phi,true);
      return phi;
    fi;
    m      := 2 * rank;
    D      := AllResidueClassesModulo(m);
    RCWA_Z := RCWA(Integers);
    gamma  := List([1..rank],
                   k->RepresentativeAction(RCWA_Z,
                                           Difference(Integers,D[2*k-1]),
                                           D[2*k]));
    for i in [1..rank] do
      SetIsTame(gamma[i],false); SetOrder(gamma[i],infinity);
    od;
    image := Group(gamma);
    SetSize(image,infinity); SetIsTame(image,false);
    SetRankOfFreeGroup(image,rank);
    phi := EpimorphismByGeneratorsNC(F,image);
    SetIsBijective(phi,true);
    return phi;
  end );

#############################################################################
##
#M  IsomorphismRcwaGroupOverZ( <F> ) . . . for free products of finite groups
#M  IsomorphismRcwaGroup( <F> )
##
##  This method uses the Table-Tennis Lemma -- see e.g. Section II.B. in
##  the book Pierre de la Harpe: Topics in Geometric Group Theory.
##
##  The method uses regular permutation representations of the factors G_r
##  (r = 0..m-1) of the free product on residue classes modulo n_r := |G_r|.
##
##  The basic idea is that since point stabilizers in regular permutation
##  groups are trivial, all non-identity elements map any of the permuted
##  residue classes into their complements.
##
##  To get into a situation where the Table-Tennis Lemma is applicable,
##  the method computes conjugates of the images of the mentioned permutation
##  representations under bijective rcwa mappings g_r which satisfy
##  0(n_r)^g_r = Z \ r(m).
##
InstallMethod( IsomorphismRcwaGroupOverZ,
               "for free products of finite groups (RCWA)",
               ReturnTrue, [ IsFpGroup and HasFreeProductInfo ], 0,

  function ( F )

    local  phi, img, gens, gensF, info, groups, degs, embs, embsF, embnrs,
           regreps, rcwareps, conjisos, conjelms, r, m, i;

    info := FreeProductInfo(F); groups := Filtered(info.groups,IsNonTrivial);
    if not ForAll(groups,IsFinite) or Length(groups) < 2
      or ForAll(groups,G->Size(G)<=2) # We can use the Table-Tennis Lemma
    then TryNextMethod(); fi;         # only if one group has order >= 3.
    m := Length(groups); degs := List(groups,Size);
    regreps  := List(groups,RegularActionHomomorphism);
    rcwareps := List(regreps,phi->IsomorphismRcwaGroup(Image(phi)));
    conjelms := List([0..m-1],r->RepresentativeAction(RCWA(Integers),
                                 ResidueClass(0,degs[r+1]),
                                 Difference(Integers,ResidueClass(r,m))));
    conjisos := List([1..m],i->ConjugatorIsomorphism(Image(rcwareps[i]),
                                                     conjelms[i]));
    embs     := List([1..m],i->CompositionMapping(conjisos[i],rcwareps[i],
                                                  regreps[i]));
    gensF    := GeneratorsOfGroup(F);
    embsF    := info.embeddings;
    embnrs   := List(gensF,
                     f->First([1..m],
                              i->f in GeneratorsOfGroup(Image(embsF[i]))));
    gens     := List([1..Length(gensF)],
                     i->Image(embs[embnrs[i]],
                              PreImagesRepresentative(embsF[embnrs[i]],
                                                      gensF[i])));
    img := Group(gens);
    SetSize(img,infinity); SetIsTame(img,false);
    SetFreeProductInfo(img,info);
    phi := EpimorphismByGeneratorsNC(F,img);
    SetIsBijective(phi,true);
    return phi;
  end );

#############################################################################
##
#M  IsomorphismRcwaGroupOverZ( <F> ) . . . . . . .  for free products of C2's
#M  IsomorphismRcwaGroup( <F> )
##
##  This method covers the case that all factors of the free product are
##  cyclic groups of order 2.
##
InstallMethod( IsomorphismRcwaGroupOverZ,
               "for free products of cyclic groups of order 2 (RCWA)",
               ReturnTrue, [ IsFpGroup and HasFreeProductInfo ], 0,

  function ( F )

    local  phi, phitilde, img, gens, genstilde, info,
           groups, groupstilde, m, degs;

    info   := FreeProductInfo(F);
    groups := Filtered(info.groups,IsNonTrivial);
    m      := Length(groups);
    degs   := List(groups,Size);
    if Set(degs) <> [2] then TryNextMethod(); fi;
    if m = 1 then TryNextMethod(); elif m = 2 then
      gens := [ClassReflection(0,1),ClassReflection(0,1)*ClassShift(0,1)];
      img  := Group(gens); SetIsTame(img,true); SetSize(img,infinity);
    else
      groupstilde := Concatenation(groups,[CyclicGroup(3)]);
      phitilde    := IsomorphismRcwaGroupOverZ(FreeProduct(groupstilde));
      genstilde   := GeneratorsOfGroup(Image(phitilde));
      gens        := genstilde{[1..Length(genstilde)-1]};
      img         := Group(gens);
      SetIsTame(img,false); SetSize(img,infinity);
    fi;
    phi := EpimorphismByGeneratorsNC(F,img);
    SetIsBijective(phi,true);
    return phi;
  end );

#############################################################################
##
#M  StructureDescription( <G> ). . . . . . . . . . . . for rcwa groups over Z
##
InstallMethod( StructureDescription,
               "for rcwa groups over Z (RCWA)",
               true, [ IsRcwaGroupOverZ ], 0,

  function ( G )

    local  desc, short, P, H, rank, top, bottom, ords, factors, descs, gens,
           bound, domain, induced, commgraph, e, comps, comp, comp_old, rem,
           i;

    if not IsFinitelyGeneratedGroup(G) then TryNextMethod(); fi;
    short := ValueOption("short") <> fail;

    if IsTrivial(G) then return "1"; fi;
    if   IsFinite(G)
    then return StructureDescription(Image(IsomorphismPermGroup(G))); fi;
    if HasDirectProductInfo(G) then
      factors := DirectProductInfo(G)!.groups;
      descs   := Filtered(List(factors,StructureDescription),str->str<>"1");
      for i in [1..Length(descs)] do
        if   Intersection(descs[i],"x:.*wr") <> ""
        then descs[i] := Concatenation("(",descs[i],")"); fi; 
      od;
      desc := descs[1];
      for i in [2..Length(descs)] do
        desc := Concatenation(desc," x ",descs[i]);
      od;
      if short then RemoveCharacters(desc," "); fi;
      return desc;
    fi;
    if HasWreathProductInfo(G) then
      factors := WreathProductInfo(G)!.groups;
      descs   := List(factors,StructureDescription);
      for i in [1..2] do
        if   Intersection(descs[i],"x:.*wr") <> ""
        then descs[i] := Concatenation("(",descs[i],")"); fi; 
      od;
      desc := Concatenation(descs[1]," wr ",descs[2]);
      if short then RemoveCharacters(desc," "); fi;
      return desc;
    fi;
    if HasFreeProductInfo(G) then
      factors := FreeProductInfo(G)!.groups;
      descs   := Filtered(List(factors,StructureDescription),str->str<>"1");
      for i in [1..Length(descs)] do
        if   Intersection(descs[i],"x:.*wr") <> ""
        then descs[i] := Concatenation("(",descs[i],")"); fi; 
      od;
      desc := descs[1];
      for i in [2..Length(descs)] do
        desc := Concatenation(desc," * ",descs[i]);
      od;
      if short then RemoveCharacters(desc," "); fi;
      return desc;
    fi;
    gens := DuplicateFreeList(Filtered(GeneratorsOfGroup(G),
                                       gen->not IsOne(gen)));
    List(gens,IsTame);
    if   Length(gens) = 2 and not IsAbelian(G) and List(gens,Order) = [2,2]
    then if not IsTame(Product(gens)) or Order(Product(gens)) = infinity
         then return "D0"; fi; fi;
    if Length(gens) = 2 and Set(List(gens,Order)) = [2,infinity] then
      if   Order(gens[1]) = infinity and gens[1]^gens[2] = gens[1]^-1
        or Order(gens[2]) = infinity and gens[2]^gens[1] = gens[2]^-1
      then return "D0"; fi;
    fi;
    commgraph := Filtered(Combinations([1..Length(gens)],2),
                          e->not IsEmpty(Intersection(Support(gens[e[1]]),
                                                      Support(gens[e[2]]))));
    comps := []; rem := [1..Length(gens)];
    repeat
      comp := [rem[1]];
      repeat
        comp_old := ShallowCopy(comp);
        for e in commgraph do
          if Intersection(comp,e) <> [] then comp := Union(comp,e); fi;
        od;
      until comp = comp_old;
      Add(comps,comp);
      rem := Difference(rem,comp);
    until rem = [];
    if Length(comps) > 1 then
      descs := List(comps,comp->StructureDescription(Group(gens{comp})));
      desc  := ShallowCopy(descs[1]);
      for i in [2..Length(comps)] do
        Append(desc," x ");
        if Intersection(descs[i],"x:.*wr") <> ""
        then descs[i] := Concatenation("(",descs[i],")"); fi;
        Append(desc,descs[i]);
      od;
      if short then RemoveCharacters(desc," "); fi;
      return desc;
    fi;
    if IsTame(G) then
      if IsFinite(G) then
        return StructureDescription(Image(IsomorphismPermGroup(G)));
      else
        if Length(gens) = 1 then return "Z"; fi;
        rank := RankOfKernelOfActionOnRespectedPartition(G);
        if   IsClassWiseOrderPreserving(G)
        then H := ActionOnRespectedPartition(G);
        else H := Action(G,RefinedRespectedPartitions(G)[2]); fi;
        top := StructureDescription(H);
        if short then bottom := Concatenation("Z^",String(rank)); else
          bottom := "Z";
          for i in [2..rank] do bottom := Concatenation(bottom," x Z"); od;
        fi;
        if not IsTrivial(H) then
          if   Intersection(top,"x:.") <> ""
          then top := Concatenation("(",top,")"); fi;
          if   Position(bottom,'x') <> fail
          then bottom := Concatenation("(",bottom,")"); fi;
          if short then
            desc := Concatenation(bottom,".",top);
          else
            desc := Concatenation(bottom," . ",top);
          fi;
        else desc := bottom; fi;
        return desc;
      fi;
    else
      if Length(gens) = 1 then return "Z"; fi;
      if   HasRankOfFreeGroup(G)
      then return Concatenation("F",String(RankOfFreeGroup(G))); fi;
      bound  := Lcm(List(gens,Modulus)); # some `reasonable' value
      domain := Intersection(Support(G),[-bound..bound]);
      domain := Concatenation(ShortOrbits(G,domain,100));
      if not IsEmpty(domain) then
        induced := Action(G,domain);
        top     := StructureDescription(induced);
        if   Intersection(top,"x:.") <> ""
        then top := Concatenation("(",top,")"); fi;
        desc := Concatenation("<unknown> . ",top);
      else
        if IsClassWiseOrderPreserving(G)
          and not ForAll(gens,gen->Determinant(gen)=0)
        then desc := "<unknown> . Z";
        elif not ForAll(gens,gen->Sign(gen)=1)
        then desc := "<unknown> . 2";
        else desc := "<unknown>"; fi;
      fi;
      if short then RemoveCharacters(desc," "); fi;
      return desc;
    fi;
  end );

#############################################################################
##
#M  StructureDescription( <G> ). . . . . . . . . . . . . . .  for rcwa groups
##
InstallMethod( StructureDescription,
               "for rcwa groups (RCWA)", true, [ IsRcwaGroup ], 0,

  function ( G )
    if   IsNaturalRCWA_Z(G) or IsNaturalRCWA_Z_pi(G) or IsNaturalRCWA_GFqx(G)
    then return Name(G); fi;
    if   IsFinite(G)
    then return StructureDescription(Image(IsomorphismPermGroup(G))); fi;
    return "<unknown>";
  end );

#############################################################################
##
#E  rcwagrp.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here