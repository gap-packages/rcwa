#############################################################################
##
#W  general.g                 GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains some more general pieces of code which are not direct-
##  ly related to RCWA. Some of them might perhaps later be moved into the
##  GAP Library or elsewhere.
##
Revision.general_g :=
  "@(#)$Id$";

#############################################################################
##
#M  \*( <n>, infinity ) . . . . . . . . . . for positive integer and infinity
#M  \*( infinity, <n> ) . . . . . . . . . . for infinity and positive integer
#M  \*( infinity, infinity )  . . . . . . . . . . . for infinity and infinity
##
##  In GAP 4.4.7, the GAP Library function `DirectProduct' and the general
##  method for `DirectProductOp' run into error if one of the factors is
##  known to be infinite. The methods below are installed as a workaround.
##  As maybe there are further similar places where finiteness is assumed
##  implicitly, it may be good if these methods remain available after 4.4.8.
##
InstallMethod( \*, "for positive integer and infinity (RCWA)",
               ReturnTrue, [ IsPosInt, IsInfinity ], 0,
               function ( n, infty ) return infinity; end );
InstallMethod( \*, "for infinity and positive integer (RCWA)",
               ReturnTrue, [ IsInfinity, IsPosInt ], 0,
               function ( infty, n ) return infinity; end );
InstallMethod( \*, "for infinity and infinity (RCWA)",
               ReturnTrue, [ IsInfinity, IsInfinity ], 0,
               function ( infty1, infty2 ) return infinity; end );

#############################################################################
##
#F  SearchCycle( <l> ) . . . a utility function for detecting cycles in lists
##
DeclareGlobalFunction( "SearchCycle" );

#############################################################################
##
#F  SearchCycle( <l> ) . . . a utility function for detecting cycles in lists
##
InstallGlobalFunction( SearchCycle,

  function ( l )

    local  pos, incr, refine;

    if Length(l) < 2 then return fail; fi;
    pos := 1; incr := 1;
    while Length(Set(List([1..Int((Length(l)-pos+1)/incr)],
                          i->l{[pos+(i-1)*incr..pos+i*incr-1]}))) > 1 do
      pos := pos + 1; incr := incr + 1;
      if pos + 2*incr-1 > Length(l) then return fail; fi;
    od;
    refine := SearchCycle(l{[pos..pos+incr-1]});
    if refine <> fail then return refine;
                      else return l{[pos..pos+incr-1]}; fi;
  end );

#############################################################################
##
#O  AllProducts( <D>, <k> ) . . all products of <k>-tuples of elements of <D>
##
DeclareOperation( "AllProducts", [ IsListOrCollection, IsPosInt ] );

#############################################################################
##
#M  AllProducts( <l>, <k> ) . . . . . . . . . . . . . . . . . . . . for lists
##
InstallMethod( AllProducts,
               "for lists (RCWA)", ReturnTrue, [ IsList, IsPosInt ], 0,
               function ( l, k ) return List(Tuples(l,k),Product); end );

#############################################################################
##
#F  GeneratorsAndInverses( <G> ) list of generators of <G> and their inverses
##
DeclareGlobalFunction( "GeneratorsAndInverses" );

#############################################################################
##
#F  GeneratorsAndInverses( <G> ) list of generators of <G> and their inverses
##
InstallGlobalFunction( GeneratorsAndInverses,
                       G->Concatenation(GeneratorsOfGroup(G),
                                        List(GeneratorsOfGroup(G),g->g^-1)));

#############################################################################
##
#F  EpimorphismByGenerators( <F>, <G> ) .  epi.: gen's of <F> -> gen's of <G>
#F  EpimorphismByGeneratorsNC( <F>, <G> )
##
DeclareGlobalFunction( "EpimorphismByGenerators" );
DeclareGlobalFunction( "EpimorphismByGeneratorsNC" );

#############################################################################
##
#F  EpimorphismByGenerators( <F>, <G> ) .  epi.: gen's of <F> -> gen's of <G>
#F  EpimorphismByGeneratorsNC( <F>, <G> )
##
InstallGlobalFunction( EpimorphismByGenerators,
  function ( G, H )
    return GroupHomomorphismByImages(G,H,GeneratorsOfGroup(G),
                                         GeneratorsOfGroup(H));
  end );
InstallGlobalFunction( EpimorphismByGeneratorsNC,
  function ( G, H )
    return GroupHomomorphismByImagesNC(G,H,GeneratorsOfGroup(G),
                                           GeneratorsOfGroup(H));
  end );

#############################################################################
##
#M  \in( <g>, <G> ) . for groups, checking for <g> being among the generators
##
InstallMethod(\in,
              "default method checking for <g> being among the gen's (RCWA)",
              ReturnTrue, [ IsMultiplicativeElementWithInverse, IsGroup ], 0,

  function ( g, G )
    if   g = One(G) or g in GeneratorsOfGroup(G)
    then return true;
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  IsCyclic( <G> ) . . . . . . . . . . . . . . . . default method for groups
##
InstallMethod( IsCyclic, "default method for groups (RCWA)", true,
               [ IsGroup ], 50,

  function ( G )
    if   Length(GeneratorsOfGroup(G)) = 1
    then return true;
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  AbelianInvariants( <G> ) . . .  for groups knowing an iso. to a pcp group
##
InstallMethod( AbelianInvariants,
               "for groups knowing an isomorphism to a pcp group", true,
               [ IsGroup and HasIsomorphismPcpGroup ], 0,
               G -> AbelianInvariants(Image(IsomorphismPcpGroup(G))) );

#############################################################################
##
#M  AbelianInvariants( <G> ) . .  for groups knowing an iso. to a perm.-group
##
InstallMethod( AbelianInvariants,
               "for groups knowing an isomorphism to a permutation group",
               true, [ IsGroup and HasIsomorphismPermGroup ], 0,
               G -> AbelianInvariants(Image(IsomorphismPermGroup(G))) );

#############################################################################
##
#M  DirectProductOp( <groups>, <onegroup> ) . . . . . . . . .  for pcp groups
##
InstallMethod( DirectProductOp,
               "for pcp groups (RCWA)", ReturnTrue,
               [ IsList, IsPcpGroup ], 0,

  function ( groups, onegroup )

    local  D, info, first, auts, i;

    if   IsEmpty(groups) or not ForAll(groups,IsPcpGroup)
    then TryNextMethod(); fi;

    D := groups[1]; first := [1,Length(GeneratorsOfGroup(D))+1];
    for i in [2..Length(groups)] do
      auts := List([1..Length(GeneratorsOfGroup(groups[i]))],
                   j->IdentityMapping(D));
      D    := SplitExtensionByAutomorphisms(D,groups[i],auts);
      Add(first,Length(GeneratorsOfGroup(D))+1);
    od;

    info := rec(groups := groups, first := first,
                embeddings := [ ], projections := [ ]);
    SetDirectProductInfo(D,info);

    if   ForAny(groups,grp->HasSize(grp) and not IsFinite(grp))
    then SetSize(D,infinity); fi;
    if   ForAll(groups,grp->HasSize(grp) and IsInt(Size(grp)))
    then SetSize(D,Product(List(groups,Size))); fi;

    return D;
  end );

#############################################################################
##
#E  general.g . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here