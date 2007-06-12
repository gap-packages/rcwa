#############################################################################
##
#W  read.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
#H  @(#)$Id$
##

# Read the implementation part of the package.

ReadPackage( "rcwa", "gap/general.g" );
ReadPackage( "rcwa", "gap/rcwaaux.g" );
ReadPackage( "rcwa", "gap/rcwamap.gi" );
ReadPackage( "rcwa", "gap/rcwamono.gi" );
ReadPackage( "rcwa", "gap/rcwagrp.gi" );

if    IsBound( GAPInfo.PackagesLoaded.fr )
  and CompareVersionNumbers( GAPInfo.PackagesLoaded.fr[2], "0.857142" )
then ReadPackage( "rcwa", "gap/perlist.gi" ); fi;

#############################################################################
##
#E  read.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here