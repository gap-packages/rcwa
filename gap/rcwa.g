#############################################################################
##
#W  rcwa.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains auxiliary functions for the RCWA package.
##
Revision.rcwa_g :=
  "@(#)$Id$";

# For circumventing bugs and deficiencies in 4.2
 
if not CompareVersionNumbers( VERSION, "4r3" ) then 

InstallMethod( GcdOp, "for zero polynomials", IsCollsElmsElms,
               [ IsEuclideanRing, IsPolynomial, IsPolynomial ], 100,

  function ( R, f, g )
    if   f = Zero(f) and g = Zero(f)
    then return Zero(f);
    else TryNextMethod(); fi;
  end );

InstallMethod( DefaultRingByGenerators, "for zero polynomials",
               true, [ IsCollection ], 100,

  function ( gens )
    if   not ForAll( gens, IsPolynomial )
      or not ForAll( gens, g -> g = Zero( gens[1] ) )
    then TryNextMethod(); fi;
    return PolynomialRing(GF(Characteristic(gens[1])),
                          [IndeterminateNumberOfLaurentPolynomial(gens[1])]);
  end );

MakeGAPDocDoc := ReturnFail;

fi;

#############################################################################
##
#F  BuildRCWAManual( ) . . . . . . . . . . . . . . . . . . . build the manual
##
##  This function builds the manual of the RCWA package in the file formats
##  &LaTeX;, DVI, Postscript, PDF and HTML.
##
##  This is done using the GAPDoc package by Frank Lübeck and Max Neunhöffer.
##
BuildRCWAManual := function ( )

  local  Manual, RcwaDir;

  RcwaDir := Concatenation( DIRECTORIES_LIBRARY.pkg[1]![1], "rcwa/" );
  MakeGAPDocDoc( Concatenation( RcwaDir, "doc/" ), "rcwa.xml",
                 [ "../gap/rcwa.g",
                   "../gap/z_pi.gd", "../gap/z_pi.gi",
                   "../gap/rcwamap.gd", "../gap/rcwamap.gi",
                   "../gap/rcwagrp.gd", "../gap/rcwagrp.gi",
                   "../gap/rcwalib.gi" ], "RCWA", "../../../" );
end;
MakeReadOnlyGlobal( "BuildRCWAManual" );

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
##    `"z_pi"'     & Arithmetic in the rings $\Z_\pi$.
##
##    `"integral"' & Computations with integral rcwa mappings and
##                   integral rcwa groups.
##
##    `"semilocal"'& Computations with semilocal integral rcwa
##                   mappings and semilocal integral rcwa groups.
##
##    `"modular"'  & Computations with modular rcwa mappings and
##                   modular rcwa groups.
##
##    `"all"'      & All tests.
##  \enditems
##
##  The default (if no argument is given) is `"all"'.
##  In case that all tests are to be performed, the function makes use of an
##  adaptation of the test file `tst/testall.g' of the {\GAP}-library to this
##  package. 
##
RCWATest := function ( arg )

  local  alltests, tests, test, dir;

  alltests := [ "z_pi", "integral", "semilocal", "modular" ];
  if   arg = [] or not IsSubset( alltests, arg )
  then tests := [ "all" ]; else tests := arg; fi;
  if IsString(tests) then tests := [ tests ]; fi;
  dir := Concatenation( DIRECTORIES_LIBRARY.pkg[1]![1], "rcwa/tst/" );
  for test in tests do
    if   test = "all" then Read( Concatenation( dir, "testall.g" ) );
    elif test = "z_pi"
    then ReadTest( Concatenation( dir, "z_pi.tst" ) );
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
#E  rcwa.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
