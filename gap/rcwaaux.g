#############################################################################
##
#W  rcwaaux.g                 GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
#Y  Copyright (C) 2003 by Stefan Kohl, Fachbereich Mathematik,
#Y  Universit\"at Stuttgart, Germany
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

  local  Manual, RcwaDir;

  RcwaDir := Concatenation( DIRECTORIES_LIBRARY.pkg[1]![1], "rcwa/" );
  StefansManualLayout( );
  MakeGAPDocDoc( Concatenation( RcwaDir, "doc/" ), "rcwa.xml",
                 [ "../gap/rcwaaux.g",
                   "../gap/rcwamap.gd", "../gap/rcwamap.gi",
                   "../gap/rcwagrp.gd", "../gap/rcwagrp.gi",
                   "../gap/rcwalib.gi" ], "RCWA", "../../../" );
  ResetManualLayout( );
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
##    `"integral"'   & Computations with integral rcwa mappings and
##                     integral rcwa groups.
##
##    `"semilocal"'  & Computations with semilocal integral rcwa
##                     mappings and semilocal integral rcwa groups.
##
##    `"modular"'    & Computations with modular rcwa mappings and
##                     modular rcwa groups.
##
##    `"all"'        & All tests.
##  \enditems
##
##  The default (if no argument is given) is `"all"'.
##  In case that all tests are to be performed, the function makes use of an
##  adaptation of the test file `tst/testall.g' of the {\GAP}-library to this
##  package. 
##
RCWATest := function ( arg )

  local  alltests, tests, test, dir;

  alltests := [ "integral", "semilocal", "modular" ];
  if   arg = [] or not IsSubset( alltests, arg )
  then tests := [ "all" ]; else tests := arg; fi;
  if IsString(tests) then tests := [ tests ]; fi;
  dir := Concatenation( DIRECTORIES_LIBRARY.pkg[1]![1], "rcwa/tst/" );
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

  local  dir;

  dir := Concatenation( DIRECTORIES_LIBRARY.pkg[1]![1], "rcwa/examples/" );
  Read( Concatenation( dir, "examples.g" ) );
end;
MakeReadOnlyGlobal( "RCWAReadExamples" );

#############################################################################
##
#E  rcwaaux.g . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
