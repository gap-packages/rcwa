#############################################################################
##
#W  init.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
#H  @(#)$Id$
##

DeclarePackage( "rcwa", "1.0",
  
  function ()
    if   CompareVersionNumbers( VERSION, "4r3" )
    then if   TestPackageAvailability( "gapdoc", "0.99" ) = fail
         then Info( InfoWarning, 1, 
                    "Package `RCWA' needs the GAPDoc package." );
              return false;
         else return true; fi;
    else Info( InfoWarning, 1, "Package `RCWA' needs at least GAP 4.3.");
         return false;
    fi;
  end );

# Load the GAPDoc package, if this has not been done so far.

if IsList( TestPackageAvailability( "gapdoc", "0.99" ) ) then
  OLD_BANNER := BANNER; MakeReadWriteGlobal( "BANNER" ); BANNER := false;
  RequirePackage( "gapdoc" );
  BANNER := OLD_BANNER; MakeReadOnlyGlobal( "BANNER" );
fi;

DeclarePackageAutoDocumentation( "rcwa", "doc" );

# Load the package GRAPE, if available
# (this is currently only used by the function `RcwaGraph').

if IsList( TestPackageAvailability( "grape", "4.0" ) ) then
  OLD_BANNER := BANNER; MakeReadWriteGlobal( "BANNER" ); BANNER := false;
  RequirePackage( "grape" );
  BANNER := OLD_BANNER; MakeReadOnlyGlobal( "BANNER" );
fi;

# Read the declaration part of the package.

ReadPkg( "rcwa", "banner.g" );
ReadPkg( "rcwa", "gap/z_pi.gd" );
ReadPkg( "rcwa", "gap/rcwamap.gd" );
ReadPkg( "rcwa", "gap/rcwagrp.gd" );

#############################################################################
##
#E  init.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
