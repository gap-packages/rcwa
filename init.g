#############################################################################
##
#W  init.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
#H  @(#)$Id$
##
#Y  Copyright (C) 2003 by Stefan Kohl, Fachbereich Mathematik,
#Y  Universit\"at Stuttgart, Germany
##

SetInfoLevel( InfoWarning, 0 );

DeclarePackage( "rcwa", "1.0",
  
  function ()
    if   CompareVersionNumbers( VERSION, "4r3" )
    then if   TestPackageAvailability( "resclasses", "1.0" ) = fail
         then Info( InfoWarning, 1, 
                    "Package `RCWA' needs the ResClasses package." );
              return false;
         elif TestPackageAvailability( "grape", "4.0" ) = fail
         then Info( InfoWarning, 1, 
                    "Package `RCWA' needs the GRAPE package." );
              return false;
         elif TestPackageAvailability( "gapdoc", "0.99" ) = fail
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
  LoadPackage( "gapdoc" );
  BANNER := OLD_BANNER; MakeReadOnlyGlobal( "BANNER" );
fi;

DeclarePackageAutoDocumentation( "rcwa", "doc" );

# Load the ResClasses package, if this has not been done so far.

if IsList( TestPackageAvailability( "resclasses", "1.0" ) ) then
  OLD_BANNER := BANNER; MakeReadWriteGlobal( "BANNER" ); BANNER := false;
  LoadPackage( "resclasses" );
  BANNER := OLD_BANNER; MakeReadOnlyGlobal( "BANNER" );
fi;

# Load the GRAPE package, if this has not been done so far.

if IsList( TestPackageAvailability( "grape", "4.0" ) ) then
  OLD_BANNER := BANNER; MakeReadWriteGlobal( "BANNER" ); BANNER := false;
  LoadPackage( "grape" );
  BANNER := OLD_BANNER; MakeReadOnlyGlobal( "BANNER" );
fi;

# Read the declaration part of the package.

ReadPkg( "rcwa", "banner.g" );
ReadPkg( "rcwa", "gap/rcwamap.gd" );
ReadPkg( "rcwa", "gap/rcwagrp.gd" );

SetInfoLevel( InfoWarning, 1 );

#############################################################################
##
#E  init.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
