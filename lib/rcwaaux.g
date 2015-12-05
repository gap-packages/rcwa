#############################################################################
##
#W  rcwaaux.g                 GAP4 Package `RCWA'                 Stefan Kohl
##
##  This file contains auxiliary functions for the RCWA package.
##
#############################################################################

#############################################################################
##
#S  Building the manual and testing the examples. ///////////////////////////
##
#############################################################################

#############################################################################
##
#F  RCWABuildManual( ) . . . . . . . . . . . . . . . . . . . build the manual
##
##  This function builds the manual of the RCWA package in the file formats
##  LaTeX, PDF, HTML and ASCII-text.
##
##  This is done using the GAPDoc package by Frank Lübeck and Max Neunhöffer.
##
BindGlobal( "RCWABuildManual", 

  function ( )

    local  RCWADir;

    RCWADir := GAPInfo.PackagesInfo.("rcwa")[1].InstallationPath;
    MakeGAPDocDoc( Concatenation( RCWADir, "/doc/" ), "main.xml",
                   [ "../lib/rcwaaux.g", "../lib/frdepend.gi",
                     "../lib/general.gd", "../lib/general.gi",
                     "../lib/rcwamap.gd", "../lib/rcwamap.gi",
                     "../lib/rcwamono.gd", "../lib/rcwamono.gi",
                     "../lib/rcwagrp.gd", "../lib/rcwagrp.gi" ],
                     "RCWA", "../../../" );
  end );

#############################################################################
##
#F  RCWATestExamples( ) . . . . . . . . . .  test examples in the RCWA manual
##
##  Tests the examples in the manual of the RCWA package.
##
BindGlobal( "RCWATestExamples",

  function ( )

    local  path;

    path := GAPInfo.PackagesInfo.("rcwa")[1].InstallationPath;
    RunExamples(ExtractExamples(Concatenation(path,"/doc"),
                                "main.xml",[],"Chapter"),
                rec( width := 75, compareFunction := "uptowhitespace" ) );
  end );

#############################################################################
##
#S  Test utilities. /////////////////////////////////////////////////////////
##
#############################################################################

TEST_TIMINGS := [];

#############################################################################
##
#F  RCWATestInstall( ) . . . . quick test whether RCWA is installed correctly
##
##  Performs a nontrivial computation to check whether an installation of
##  RCWA appears to work.
##
BindGlobal( "RCWATestInstall",

  function ( )

    local  RCWADir, dir;

    RCWADir := GAPInfo.PackagesInfo.("rcwa")[1].InstallationPath;
    dir := Concatenation( RCWADir, "/tst/" );
    Test( Concatenation( dir, "testinstall.tst" ) );
  end );

#############################################################################
##
#F  RCWATestAll( ) . . . . . . . . . . . . . . . . . . . . .  RCWA test suite
##
##  Runs the full test suite of the RCWA package.
##
##  The function makes use of an adaptation of the test file tst/testall.g
##  of the GAP Library to this package. 
##
BindGlobal( "RCWATestAll",

  function ( )

    local  RCWADir, dir;

    RCWADir := GAPInfo.PackagesInfo.("rcwa")[1].InstallationPath;
    dir := Concatenation( RCWADir, "/tst/" );
    Read( Concatenation( dir, "testall.g" ) );
  end );

#############################################################################
##
#F  RCWADoThingsToBeDoneBeforeTest(  )
#F  RCWADoThingsToBeDoneAfterTest(  )
##
BindGlobal( "RCWADoThingsToBeDoneBeforeTest",

  function (  )
    RESCLASSES_WARNINGLEVEL_BUFFER := InfoLevel(InfoWarning);;
    SetInfoLevel(InfoWarning,0);
    RESCLASSES_VIEWINGFORMAT_BUFFER := RESCLASSES_VIEWINGFORMAT;;
    ResidueClassUnionViewingFormat("short");
    CallFuncList(HideGlobalVariables,ONE_LETTER_GLOBALS);
  end );

BindGlobal( "RCWADoThingsToBeDoneAfterTest",

  function (  )
    CallFuncList(UnhideGlobalVariables,ONE_LETTER_GLOBALS);
    ResidueClassUnionViewingFormat(RESCLASSES_VIEWINGFORMAT_BUFFER);
    SetInfoLevel(InfoWarning,RESCLASSES_WARNINGLEVEL_BUFFER);
  end );

#############################################################################
##
#F  ReadTestWithTimings( <filename> ) . . . read test file and return timings
##
BindGlobal( "ReadTestWithTimings",

  function ( filename )

    local  timings, filewithtimings, inputlines, outputlines, isinput,
           line, nextline, pos, intest, commands, command, lastbuf, i;

    isinput := function ( line )
      if Length(line) < 1 then return false; fi;
      if line[1] = '>' then return true; fi;
      if Length(line) < 4 then return false; fi;
      if line{[1..4]} = "gap>" then return true; fi;
      return false;
    end;

    if   not IsString(filename)
    then Error("usage: ReadTestWithTimings( <filename> )"); fi;

    inputlines := SplitString(StringFile(filename),"\n");
    outputlines := []; intest := false; commands := []; command := [];
    for pos in [1..Length(inputlines)] do
      line := inputlines[pos];
      Add(outputlines,line);
      if PositionSublist(line,"START_TEST") <> fail then intest := true; fi;
      if PositionSublist(line,"STOP_TEST") <> fail then intest := false; fi;
      if intest then
        if isinput(line) then Add(command,line); fi;
        nextline := inputlines[pos+1];
        if not isinput(line) and isinput(nextline) then
          Add(commands,[pos-1,JoinStringsWithSeparator(command,"\n")]);
          command := [];
          Add(outputlines,"gap> lastbuf := [last,last2,last3];;");
          Add(outputlines,"gap> runtime := Runtime()-TEST_START_TIME;;");
          Add(outputlines,"gap> Add(TEST_TIMINGS,runtime);");
          Add(outputlines,"gap> TEST_START_TIME := Runtime();;");
          Add(outputlines,"gap> last3 := lastbuf[3];;");
          Add(outputlines,"gap> last2 := lastbuf[2];;");
          Add(outputlines,"gap> last1 := lastbuf[1];;");
        fi;
      fi;
    od;
    outputlines := JoinStringsWithSeparator(outputlines,"\n");
    filename := SplitString(filename,"/");
    filename := filename[Length(filename)];
    filewithtimings := Filename(DirectoryTemporary(),filename);
    FileString(filewithtimings,outputlines);
    Unbind(TEST_TIMINGS);
    BindGlobal("TEST_TIMINGS",[]);
    MakeReadWriteGlobal("TEST_TIMINGS");
    BindGlobal("TEST_START_TIME",Runtime());
    MakeReadWriteGlobal("TEST_START_TIME"); 
    Test(filewithtimings);
    timings := TEST_TIMINGS;
    UnbindGlobal("TEST_TIMINGS");
    UnbindGlobal("TEST_START_TIME");
    if   Length(timings) <> Length(commands)
    then Error("ReadTestWithTimings: #commands <> #timings"); fi;
    return List([1..Length(commands)],i->[commands[i],timings[i]]);
  end );

#############################################################################
##
#F  ReadTestCompareRuntimes( <filename> [,<timingsdir> [,<createreference>]])
##
BindGlobal( "ReadTestCompareRuntimes",

  function ( arg )

    local  filename, timingsdir, createreference, testdir,
           timingsname, slashpos, oldtimings, newtimings, testnrs,
           changes, changed, runtimechangesignificance, threshold, n, i;

    runtimechangesignificance := function ( oldtime, newtime )
      return AbsInt(newtime-oldtime)/(10*RootInt(oldtime)+100);
    end;

    filename := arg[1];
    slashpos := Positions(filename,'/');
    slashpos := slashpos[Length(slashpos)];
    testdir  := filename{[1..slashpos]};
    if   Length(arg) >= 2
    then timingsdir := arg[2]; else timingsdir := testdir; fi;
    if   Length(arg) >= 3
    then createreference := arg[3]; else createreference := false; fi;
    if not IsString(filename) or not IsBool(createreference) then
      Error("usage: ReadTestCompareTimings( <filename> ",
            "[, <createreference> ] )");
    fi;
    timingsname := ReplacedString(filename,testdir,timingsdir);
    timingsname := ReplacedString(timingsname,".tst",".runtimes");
    if   not IsExistingFile(timingsname)
    then createreference := true;
    else oldtimings := ReadAsFunction(timingsname)(); fi;
    newtimings := ReadTestWithTimings(filename);
    if createreference then
      PrintTo(timingsname,"return ",newtimings,";\n");
    else
      n := Length(oldtimings);
      if Length(newtimings) < n or TransposedMat(newtimings)[1]{[1..n]}
                                <> TransposedMat(oldtimings)[1]
      then
        Info(InfoWarning,1,"Test file ",filename);
        Info(InfoWarning,1,"has changed, thus performance ",
                           "cannot be compared.");
        Info(InfoWarning,1,"Please create new reference timings.");
      else
        testnrs := [1..n];
        changes := List([1..n],
                        i->runtimechangesignificance(newtimings[i][2],
                                                     oldtimings[i][2]));
        SortParallel(-changes,testnrs);
        threshold := 1; # significance threshold for runtime change
        changed := Filtered(testnrs,i->changes[i]>threshold);
        for i in changed do
          Print("Line ",oldtimings[i][1][1],": ");
          if   newtimings[i][2] < oldtimings[i][2]
          then Print("speedup "); else Print("slowdown "); fi;
          Print(oldtimings[i][2],"ms -> ",newtimings[i][2],"ms\n");
          Print(oldtimings[i][1][2],"\n");
        od;
      fi;
    fi;
  end );

#############################################################################
##
#F  RCWACheckDatabaseOfGroupsGeneratedBy3ClassTranspositions( startmod )
##
##  This function checks the data library of groups generated by 3 class
##  transpositions which interchange residue classes with moduli <= 6.
##  It raises an error if there is a difference between a database entry and
##  the result of an attempt to recompute that entry. The function runs rela-
##  tively long, and it is recommended to set the `InfoLevel' of `InfoRCWA'
##  to 2 in order to get information on the progress of the checks.
##
BindGlobal( "RCWACheckDatabaseOfGroupsGeneratedBy3ClassTranspositions",

  function ( startmod )

    local  data, cts, grps, sizes, mods, modset, errors,
           pos, i, m, n, m0, n0;

    Info(InfoRCWA,2,"Checking database of groups generated by 3 class ",
                    "transpositions ...");

    data := LoadDatabaseOfGroupsGeneratedBy3ClassTranspositions();

    cts  := List(ClassPairs(6),ClassTransposition);;
    grps := List(Combinations(cts,3),Group);;

    if   cts <> data.cts or grps <> data.grps
    then Error("*** List of groups is corrupted !!! ***"); fi;

    mods  := data.mods;
    sizes := data.sizes;

    modset := Filtered(Set(mods),m->m>=startmod);
    errors := [];

    for m in modset do
      Info(InfoRCWA,2,"Checking groups with modulus m = ",m);
      pos := Positions(mods,m);
      Info(InfoRCWA,2,"There are ",Length(pos)," such groups.");
      Info(InfoRCWA,2,"They have ",Length(Set(sizes{pos})),
                      " different orders.");
      for i in pos do
        n  := sizes[i];
        m0 := Mod(grps[i]:AssumeIsTame);
        n0 := Size(grps[i]);
        Info(InfoRCWA,2,"|grps[",i,"]| = ",n0);
        if m0 <> m or n0 <> n then
          if m0 <> m then Error("** Modulus discrepancy !!! ***"); fi;
          if n0 <> n then Error("** Order discrepancy !!! ***"); fi;
          Add(errors,rec(i:=i,m_wrong:=m ,n_wrong:=n,
                              m_right:=m0,n_right:=n0));
          Print("Errors =\n",errors,"\n");
        fi;
      od;
    od;

    return errors;
  end );

#############################################################################
##
#S  Other. //////////////////////////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#F  CompressWhitespace( <src>, <dest> )
##
##  Utility function used to compress whitespace in data files.
##
BindGlobal( "CompressWhitespace",

  function ( src, dest )

    local  str;

    str := StringFile(src);
    str := ReplacedString(str,", ",",");
    str := ReplacedString(str," ]","]");
    str := ReplacedString(str,"[ ","[");
    str := ReplacedString(str,"  "," ");
    str := ReplacedString(str," \n],","],\n");
    FileString(dest,str);
  end );

ResidueClassUnionViewingFormat( "short" );

#############################################################################
##
#E  rcwaaux.g . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here