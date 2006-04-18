#############################################################################
##
#W  rcwaaux.g                 GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains auxiliary functions for the RCWA package.
##
Revision.rcwaaux_g :=
  "@(#)$Id$";

#############################################################################
##
#F  RCWABuildManual( ) . . . . . . . . . . . . . . . . . . . build the manual
##
##  This function builds the manual of the RCWA package in the file formats
##  &LaTeX;, DVI, Postscript, PDF and HTML.
##
##  This is done using the GAPDoc package by Frank L\"ubeck and
##  Max Neunh\"offer.
##
RCWABuildManual := function ( )

  local  Manual, RCWADir;

  RCWADir := GAPInfo.PackagesInfo.("rcwa")[1].InstallationPath;
  MakeGAPDocDoc( Concatenation( RCWADir, "/doc/" ), "rcwa.xml",
                 [ "../gap/rcwaaux.g",
                   "../gap/rcwamap.gd", "../gap/rcwamap.gi",
                   "../gap/rcwagrp.gd", "../gap/rcwagrp.gi" ],
                   "RCWA", "../../../" );
end;
MakeReadOnlyGlobal( "RCWABuildManual" );

#############################################################################
##
#F  RCWATest( [ <test1> [, <test2> [, ... ]]] ) . . . . . . . read test files
##
##  Performs tests of the RCWA package.
##
##  The arguments <test1>, <test2>, ..., if present, are names of tests.
##
##  Available tests are:
##
##  \beginitems
##    `"integral"'   & Computations with rcwa mappings of Z
##                     and rcwa groups over Z.
##
##    `"semilocal"'  & Computations with rcwa mappings of /
##                     rcwa groups over semilocalizations of Z.
##
##    `"modular"'    & Computations with rcwa mappings of /
##                     rcwa groups over polynomial rings GF(q)[x].
##
##    `"all"'        & All tests.
##  \enditems
##
##  The default (if no argument is given) is `"all"'.
##  In case that all tests are to be performed, the function makes use of
##  an adaptation of the test file `tst/testall.g' of the {\GAP} Library to
##  this package. 
##
RCWATest := function ( arg )

  local  alltests, tests, test, RCWADir, dir;

  alltests := [ "integral", "semilocal", "modular" ];
  if   arg = [] or not IsSubset( alltests, arg )
  then tests := [ "all" ]; else tests := arg; fi;
  if IsString(tests) then tests := [ tests ]; fi;
  RCWADir := GAPInfo.PackagesInfo.("rcwa")[1].InstallationPath;
  dir := Concatenation( RCWADir, "/tst/" );
  for test in tests do
    if   test = "all" then Read( Concatenation( dir, "testall.g" ) );
    elif test = "integral"
    then ReadTest( Concatenation( dir, "integral.tst" ) );
    elif test = "semilocal"
    then ReadTest( Concatenation( dir, "semiloc.tst" ) );
    elif test = "modular"
    then ReadTest( Concatenation( dir, "modular.tst" ) );
    fi;
  od;
end;
MakeReadOnlyGlobal( "RCWATest" );

#############################################################################
##
#F  RCWAReadExamples( ) . . . . . . . . . . . . . . . . .  read examples file
##
RCWAReadExamples := function ( )

  local  RCWADir;

  RCWADir := GAPInfo.PackagesInfo.("rcwa")[1].InstallationPath;
  Read( Concatenation( RCWADir, "/examples/examples.g" ) );
end;
MakeReadOnlyGlobal( "RCWAReadExamples" );

ResidueClassUnionViewingFormat( "short" );

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
#E  rcwaaux.g . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here