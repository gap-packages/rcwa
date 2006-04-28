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
#E  general.g . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here