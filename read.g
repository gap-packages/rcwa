#############################################################################
##
#W  read.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
##  Read the implementation part of the package.
##
#############################################################################

ReadPackage( "rcwa", "gap/rcwaaux.g" );
ReadPackage( "rcwa", "gap/general.gi" );
ReadPackage( "rcwa", "gap/rcwamap.gi" );
ReadPackage( "rcwa", "gap/rcwamono.gi" );
ReadPackage( "rcwa", "gap/rcwagrp.gi" );

if   IsPackageMarkedForLoading( "fr", "1.1.3" )
then ReadPackage( "rcwa", "gap/frdepend.gi" ); fi;

#############################################################################
##
#E  read.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here