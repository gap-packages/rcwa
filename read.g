#############################################################################
##
#W  read.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
#H  @(#)$Id$
##
#Y  Copyright (C) 2002 by Stefan Kohl, Fachbereich Mathematik,
#Y  Universit\"at Stuttgart, Germany
##

# Read the implementation part of the package.

SetInfoLevel( InfoWarning, 0 );

ReadPkg( "rcwa", "gap/rcwaaux.g" );
ReadPkg( "rcwa", "gap/z_pi.gi" );
ReadPkg( "rcwa", "gap/resclass.gi" );
ReadPkg( "rcwa", "gap/rcwamap.gi" );
ReadPkg( "rcwa", "gap/rcwagrp.gi" );
ReadPkg( "rcwa", "gap/rcwalib.gi" );

SetInfoLevel( InfoWarning, 1 );

#############################################################################
##
#E  read.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
