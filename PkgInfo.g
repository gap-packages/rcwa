####################################################################################################
##
##  PkgInfo.g                           GAP4 Package `RCWA'                              Stefan Kohl
##  
#H  @(#)$Id$
##
#Y  Copyright (C) 2002 by Stefan Kohl, Fachbereich Mathematik,
#Y  Universit\"at Stuttgart, Germany
##
##  Preliminary, not yet to be distributed !!!
##
##  None of the files on my webpage referred to from here is currently existing.
##

SetPackageInfo( rec(

PkgName          := "RCWA",
Version          := "1.0",
Date             := "21/12/2002",
ArchiveURL       := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa/rcwa-1.0",
ArchiveFormats   := ".zoo",
Persons          := [
                      rec( LastName      := "Kohl",
                           FirstNames    := "Stefan",
                           IsAuthor      := true,
                           IsMaintainer  := true,
                           Email         := "kohl@mathematik.uni-stuttgart.de",
                           WWWHome       := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/",
                           PostalAddress := Concatenation("Stefan Kohl\n",
                                                          "Institut für Geometrie und Topologie\n",
                                                          "Pfaffenwaldring 57\n",
                                                          "Universität Stuttgart\n",
                                                          "70550 Stuttgart\n",
                                                          "Germany"),
                           Place         := "Stuttgart / Germany",
                           Institution   := "University of Stuttgart"
                         )
                    ],
Status           := "dev",
CommunicatedBy   := "",
AcceptDate       := "",
README_URL       := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa/README.rcwa",
PkgInfoURL       := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa/PkgInfo.g",
AbstractHTML     := "This package deals with some kind of infinite permutation groups over rings.",
PackageWWWHome   := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa.html",
PackageDoc       := rec(
                         BookName  := "RCWA",
                         Archive   := Concatenation("http://www.cip.mathematik.uni-stuttgart.de/",
                                                    "~kohlsn/rcwa/rcwa-1.0doc-win.zip"),
                         HTMLStart := "doc/manual.html",
                         PDFFile   := "doc/manual.pdf",
                         SixFile   := "doc/manual.six",
                         LongTitle := "[R]esidue [C]lass-[W]ise [A]ffine representations of groups",
                         AutoLoad  := false
                       ),
Dependencies     := rec(
                         GAP                    := ">=4.3",
                         NeededOtherPackages    := [ ["GAPDoc",">=0.99"], ["GRAPE",">=4.0"] ],
                         SuggestedOtherPackages := [ ],
                         ExternalConditions     := [ ]
                       ),
AvailabilityTest := ReturnTrue,
BannerString     := Concatenation( "\nLoading RCWA 1.0",
                                   " ([R]esidue [C]lass-[W]ise [A]ffine mappings and groups)",
                                   "\nby Stefan Kohl, kohl@mathematik.uni-stuttgart.de\n\n" ),
AutoLoad         := false,
TestFile         := "tst/testall.g",
Keywords         := [ "Infinite permutation groups", "Permutation groups over rings" ]

) );

####################################################################################################
##
#E  PkgInfo.g  . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
