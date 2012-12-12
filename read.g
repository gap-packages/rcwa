#############################################################################
##
#W  read.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
##  Read the implementation part of the package.
##
#############################################################################

ReadPackage( "rcwa", "lib/rcwaaux.g" );
ReadPackage( "rcwa", "lib/general.gi" );
ReadPackage( "rcwa", "lib/rcwamap.gi" );
ReadPackage( "rcwa", "lib/rcwamono.gi" );
ReadPackage( "rcwa", "lib/rcwagrp.gi" );

if   IsPackageMarkedForLoading( "fr", "1.1.3" )
then ReadPackage( "rcwa", "lib/frdepend.gi" ); fi;

#############################################################################
##
#E  read.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here