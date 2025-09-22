####################################################################################################
##
##  PackageInfo.g                         GAP4 Package `RCWA'                            Stefan Kohl
##
####################################################################################################

SetPackageInfo( rec(

PackageName      := "RCWA",
Subtitle         := "Residue-Class-Wise Affine Groups",
Version          := "4.8.0",
Date             := "22/09/2025", # dd/mm/yyyy format
License          := "GPL-2.0-or-later",
Persons          := [
                      rec( LastName      := "Kohl",
                           FirstNames    := "Stefan",
                           IsAuthor      := true,
                           IsMaintainer  := true,
                           Email         := "sk239@st-andrews.ac.uk",
                           WWWHome       := "https://stefan-kohl.github.io/"
                         )
                    ],
Status           := "accepted",
CommunicatedBy   := "Bettina Eick (Braunschweig)",
AcceptDate       := "04/2005",


PackageWWWHome  := "https://gap-packages.github.io/rcwa/",
README_URL      := Concatenation( ~.PackageWWWHome, "README.md"        ),
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/gap-packages/rcwa",
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/rcwa-", ~.Version ),
ArchiveFormats   := ".tar.gz",

AbstractHTML     := Concatenation("This package provides implementations of algorithms and methods",
                                  " for computation in certain infinite permutation groups."),
PackageDoc       := rec(
                         BookName         := "RCWA",
                         ArchiveURLSubset := ["doc"],
                         HTMLStart        := "doc/chap0_mj.html",
                         PDFFile          := "doc/manual.pdf",
                         SixFile          := "doc/manual.six",
                         LongTitle        := "[R]esidue-[C]lass-[W]ise [A]ffine groups",
                       ),
Dependencies     := rec(
                         GAP                    := ">=4.12.0",
                         NeededOtherPackages    := [ ["ResClasses",">=4.7.2"], ["GRAPE",">=4.7"],
                                                     ["Polycyclic",">=2.11"], ["FR",">=2.2.1"],
                                                     ["GAPDoc",">=1.5.1"], ["Utils",">=0.40"] ],
                         SuggestedOtherPackages := [ ],
                         ExternalConditions     := [ ]
                       ),
AvailabilityTest := function ( )
                      if GAPInfo.BytesPerVariable = 4 then
                        LogPackageLoadingMessage( PACKAGE_WARNING,
                                                  [ "you are running GAP in legacy 32-bit mode - ",
                                                    "not everything might work." ] );
                      fi;
                      return true;
                    end,
BannerString     := Concatenation( "\nLoading RCWA ", ~.Version,
                                   " ([R]esidue-[C]lass-[W]ise [A]ffine groups)",
                                   "\n  by Stefan Kohl, sk239@st-andrews.ac.uk.",
                                   "\nSee ?RCWA:About for information about the package.\n\n" ),
TestFile         := "tst/testall.g",
Keywords         := [ "infinite permutation groups", "permutation groups over rings",
                      "combinatorial group theory", "residue-class-wise affine groups",
                      "residue-class-wise affine mappings",
                      "Collatz conjecture", "3n+1 conjecture" ],

AutoDoc := rec(
    TitlePage := rec(
        Copyright := """
&copyright; 2003 - 2018 by Stefan Kohl. <P/>

&RCWA; is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 2 of the License, or
(at your option) any later version. <P/>

&RCWA; is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details. <P/>

For a copy of the GNU General Public License, see 
the file <F>GPL</F> in the <F>etc</F> directory of the &GAP;
distribution or see <URL>https://www.gnu.org/licenses/gpl.html</URL>.
<Alt Only="LaTeX">\vspace{-1cm}</Alt>
        """,
        Abstract := """<#Include SYSTEM "abstract.xml">""",
        Acknowledgements := """
I am grateful to John P. McDermott for the discovery that the group
discussed in Section&nbsp;<Ref Label="sec:ThompsonsGroupV"/> is
isomorphic to Thompson's Group V in July 2008, and to Laurent Bartholdi
for his hint on how to construct wreath products of residue-class-wise
affine groups with&nbsp;(&ZZ;,+) in April 2006.
Further, I thank Bettina&nbsp;Eick for communicating this package
and for her valuable suggestions on its manual in the time before its
first public release in April 2005.
Last but not least I thank the two anonymous referees for their
constructive criticism and their helpful suggestions.
        """,
    ),
),

) );

####################################################################################################
##
#E  PackageInfo.g  . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
