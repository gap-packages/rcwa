#############################################################################
##
#W  rcwa.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
#H  @(#)$Id$
##
#Y  Copyright (C) 2002 by Stefan Kohl, Mathematisches Institut B,
#Y  Universit\"at Stuttgart, Germany
##
##  This file contains auxiliary functions for the RCWA package.
##
Revision.rcwa_g :=
  "@(#)$Id$";

# Missing `String' method for Integers.

InstallMethod( String, "for Integers", true, [ IsIntegers ], 0,
               Ints -> "Integers" );

#############################################################################
##
#F  ColorPrompt( b ) . . . . . . . . . . . . . . . . . . . the coloring stuff
##
##  This encloses Frank L\"ubeck's code for coloring GAP prompts, user input
##  and online help texts.
##  Coloring can be switched off by setting the option `BlackAndWhite' when
##  loading RCWA.
##
if ValueOption( "BlackAndWhite" ) <> true then
  
  STDOUT := OutputTextUser();;
  PrintPromptHook:=CPROMPT;; EndLineHook:=function() end;;

  if not IsBound( ColorPrompt ) then  

    ColorPrompt := function( b )
  
      if b = false then
        Unbind(PrintPromptHook); Unbind(EndLineHook); return;
      fi;

      # print the prompt

      PrintPromptHook := function( )
  
        local cp;
  
        cp := CPROMPT();
        if cp = "gap> " then cp := "gap> "; fi;
        # different color for brk...> prompts
        if Length(cp)>0 and cp[1] = 'b' then
          WriteAll(STDOUT, "\033[1m\033[31m");
        else
          WriteAll(STDOUT, "\033[1m\033[34m");
        fi;
        # use this instead of Print such that the column counter for the 
        # command line editor is correct
        PRINT_CPROMPT(cp);
        # another color for input
        WriteAll(STDOUT, "\033[0m\033[31m");
      end;

      # reset attributes before going to the next line

      EndLineHook := function()
        WriteAll(STDOUT, "\033[0m");
      end;
    end;
    MakeReadOnlyGlobal( "ColorPrompt" );

  fi;

  Unbind(PrintPromptHook); Unbind(EndLineHook);

  ColorPrompt(true);
  ANSI_COLORS := true; # switch on coloring of online help texts

fi;

#############################################################################
##
#F  BuildRCWAManual( ) . . . . . . . . . . . . . . . . . . . build the manual
##
##  This function builds the manual of the RCWA package in the file formats
##  &LaTeX;, DVI, Postscript, PDF and HTML.
##
##  This is done using the GAPDoc package by Frank LÅbeck and Max Neunh˜ffer.
##
BuildRCWAManual := function ( )

  local  Manual, RcwaDir;

  RcwaDir := Concatenation( DIRECTORIES_LIBRARY.pkg[1]![1], "rcwa/" );
  MakeGAPDocDoc( Concatenation( RcwaDir, "doc/" ), "rcwa.xml",
                 [ "../gap/rcwa.g",
                   "../gap/z_pi.gd", "../gap/z_pi.gi",
                   "../gap/resclass.gd", "../gap/resclass.gi",
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
##    `"z_pi"'       & Arithmetic in the rings $\Z_\pi$.
##
##    `"resclasses"' & Computations with residue class unions.
##
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

  alltests := [ "z_pi", "resclasses", "integral", "semilocal", "modular" ];
  if   arg = [] or not IsSubset( alltests, arg )
  then tests := [ "all" ]; else tests := arg; fi;
  if IsString(tests) then tests := [ tests ]; fi;
  dir := Concatenation( DIRECTORIES_LIBRARY.pkg[1]![1], "rcwa/tst/" );
  for test in tests do
    if   test = "all" then Read( Concatenation( dir, "testall.g" ) );
    elif test = "z_pi"
    then ReadTest( Concatenation( dir, "z_pi.tst" ) );
    elif test = "resclasses"
    then ReadTest( Concatenation( dir, "resclass.tst" ) );
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
