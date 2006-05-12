#############################################################################
##
#W  general.g                 GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains some more general pieces of code which are not direct-
##  ly related to RCWA. Some of them might perhaps later be moved into the
##  GAP Library.
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
#F  GeneratorsAndInverses( <G> )
##
InstallGlobalFunction( GeneratorsAndInverses,
                       G->Concatenation(GeneratorsOfGroup(G),
                                        List(GeneratorsOfGroup(G),g->g^-1)));

#############################################################################
##
#F  EpimorphismByGenerators( <G>, <H> )
#F  EpimorphismByGeneratorsNC( <G>, <H> )
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
#E  general.g . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here