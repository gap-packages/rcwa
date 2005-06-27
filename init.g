#############################################################################
##
#W  init.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
#H  @(#)$Id$
##

# Read the declaration part of the package.

ReadPackage( "rcwa", "gap/rcwamap.gd" );
ReadPackage( "rcwa", "gap/rcwagrp.gd" );

if   not CompareVersionNumbers(VERSION,"4.5")
then ReadPackage( "rcwa", "gap/compat44.g" ); fi;

#############################################################################
##
#E  init.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here