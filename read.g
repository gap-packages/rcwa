#############################################################################
##
#W  read.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
#H  @(#)$Id$
##

# Read the implementation part of the package.

SetInfoLevel( InfoWarning, 0 );

ReadPkg( "rcwa", "gap/rcwaaux.g" );
ReadPkg( "rcwa", "gap/rcwamap.gi" );
ReadPkg( "rcwa", "gap/rcwagrp.gi" );
ReadPkg( "rcwa", "gap/rcwalib.gi" );

SetInfoLevel( InfoWarning, 1 );

#############################################################################
##
#E  read.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
