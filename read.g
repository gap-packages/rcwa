#############################################################################
##
#W  read.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
#H  @(#)$Id$
##

# Load the rudimentary functionality for floats, if not already available
# from the library.

if not IsBound( IsFloat ) then ReadPackage( "rcwa", "gap/float.g" ); fi;

# Read the implementation part of the package.

ReadPackage( "rcwa", "gap/rcwaaux.g" );
ReadPackage( "rcwa", "gap/rcwamap.gi" );
ReadPackage( "rcwa", "gap/rcwagrp.gi" );

#############################################################################
##
#E  read.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here