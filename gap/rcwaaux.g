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
                   "../gap/rcwagrp.gd", "../gap/rcwagrp.gi",
                   "../gap/rcwalib.gi" ], "RCWA", "../../../" );
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

#############################################################################
##
#C  IsFloat . . . . . . . . . . . . . . . . . . . . . . . . . . . . . C float
##
DeclareSynonym( "IsFloat", IS_FLOAT );

#############################################################################
##
#M  AbsoluteValue( x ) . . . . . . . . . . . . . . . . . . . . . . for floats
##
InstallOtherMethod( AbsoluteValue,
                    "for floats", true, [ IsFloat ], 0,

  function ( x )
    if x < FLOAT_INT(0) then return -x; else return x; fi;
  end );

#############################################################################
##
#O  Float( x ) . . . . . . . . . . . . . . . . . floating point approximation
##
DeclareOperation( "Float", [ IsObject ] );

#############################################################################
##
#M  Float( n ) . . . . . . . . . . . . . . . . . . . . . . . . . for integers
##
InstallMethod( Float,
               "for integers", true, [ IsInt ], 0, n -> FLOAT_INT(n) );

#############################################################################
##
#M  Float( x ) . . . . . . . . . . . . . . . . . . . . . . . .  for rationals
##
InstallMethod( Float,
               "for rationals", true, [ IsRat ], 0,
               x -> FLOAT_INT(  NumeratorRat(x))/
                    FLOAT_INT(DenominatorRat(x)) );

#############################################################################
##
#E  rcwaaux.g . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here

