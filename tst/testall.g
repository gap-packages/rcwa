#############################################################################
##
#W  testall.g                GAP4 Package `RCWA'                 Frank Celler
##                                                                Stefan Kohl
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
##
##  This is an adaptation of the test file for the GAP library to the
##  `RCWA' - package.
##

#############################################################################
##
#F  START_TEST( <id> )  . . . . . . . . . . . . . . . . . . . start test file
##
start_TEST := START_TEST;

START_TIME := 0;
STONE_NAME := "";

START_TEST := function( name )
    FlushCaches();
    RANDOM_SEED(1);
    GASMAN("collect");
    START_TIME := Runtime();
    STONE_NAME := name;
end;

#############################################################################
##
#F  STOP_TEST( <file>, <fac> )  . . . . . . . . . . . . . . .  stop test file
##
stop_TEST := STOP_TEST;

STONE_RTIME := 0;
STONE_STONE := 0;
STONE_FILE  := 0;
STONE_SUM   := 0;
STONE_FSUM  := 0;
STONE_PROD  := 1;
STONE_COUNT := 0;

STOP_TEST := function( file, fac )
    local   time;

    STONE_FILE  := file;
    STONE_RTIME := Runtime() - START_TIME;
    if STONE_RTIME > 500  then
        STONE_STONE := QuoInt( fac, STONE_RTIME );
        STONE_SUM   := STONE_SUM + STONE_RTIME;
        STONE_FSUM  := STONE_FSUM + fac;
        STONE_PROD  := STONE_PROD*STONE_STONE;
        STONE_COUNT := STONE_COUNT + 1;
    else
        STONE_STONE := 0;
    fi;
end;

#############################################################################
##
#F  SHOW_STONES( <next> ) . . . . . . . . . . . . . . . . .  show GAP4 stones
##
STONE_ALL := [];

SHOW_STONES := function( next )
    Print( FormattedString(STONE_FILE,-16), "    ",
           FormattedString(STONE_STONE,8), "       ",
           FormattedString(STONE_RTIME,8) );
    Add( STONE_ALL, STONE_STONE );
    if 0 < next and STONE_FSUM <> 0  then
        Print( "    (next ~ ", Int(STONE_SUM*next*10/STONE_FSUM),
               " sec)\n" );
    else
        Print("\n");
    fi;
end;

#############################################################################
##
#F  TEST_FILES  . . . . . . . . . . . . . . . . . . . . .  list of test files
##
##  the following list contains the filename and  the scaling factor given to
##  `STOP_TEST' at the end of the test file.  The file  names are relative to
##  the test directory.
##
##  The list can be produced using:
##
##  grep -h "STOP_TEST" *.tst | sed -e 's:^gap> STOP_TEST( ":[ ":' | \
##  sed -e 's: );: ],:'
##
TEST_FILES := [ [ "z_pi.tst"     ,    3000000 ],
                [ "integral.tst" , 3100000000 ],
                [ "semiloc.tst"  ,  100000000 ],
                [ "modular.tst"  ,  160000000 ] ];

Sort( TEST_FILES, function(a,b) return a[2] < b[2]; end );


#############################################################################
##
#X  read all test files
##
Print("You should start GAP4 using:  `gap -N -M -A -x 80 -r -m 30m'. The more\n");
Print("GAP4stones you get, the faster your  system is.  The runtime of\n");
Print("the following tests (in general)  increases.  You should expect\n");
Print("about 10000 GAP4stones on a Pentium 5, 133 MHz,  about 28000 on\n");
Print("a Pentium Pro, 200 Mhz.  The `next' time is an approximation of\n");
Print("the running time for the next test.\n");
Print("\n");
Print("Architecture: ", GAP_ARCHITECTURE, "\n");
Print("\n");
Print("test file         GAP4stones     time(msec)\n");
Print("-------------------------------------------\n");

infoRead1 := InfoRead1;  InfoRead1 := Ignore;
infoRead2 := InfoRead2;  InfoRead2 := Ignore;

TestDir := Concatenation(DirectoriesLibrary("pkg")[1]![1],"rcwa/tst/");
TestDir := [ Directory(TestDir) ];

for i  in [ 1 .. Length(TEST_FILES) ]  do
    name := Filename( TestDir, TEST_FILES[i][1] );
    if i < Length(TEST_FILES)  then
        next := TEST_FILES[i+1][2] / 10^4;
    else
        next := 0;
    fi;
    Print("testing: ",name,"\n");
    ReadTest(name);
    SHOW_STONES(next);
od;

Print("-------------------------------------------\n");
if STONE_COUNT=0 then
  STONE_COUNT:=1;
fi;
Print( FormattedString("total",-16), "    ",
       FormattedString(RootInt(STONE_PROD,STONE_COUNT),8), "       ",
       FormattedString(STONE_SUM,8), "\n" );
Print("\n");

InfoRead1  := infoRead1;
InfoRead2  := infoRead2;
START_TEST := start_TEST;
STOP_TEST  := stop_TEST;

#############################################################################
##
#E  testall.g . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here