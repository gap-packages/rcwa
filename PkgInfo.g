####################################################################################################
##
##  PkgInfo.g                           GAP4 Package `RCWA'                              Stefan Kohl
##  
#H  @(#)$Id$
##

SetPackageInfo( rec(

PkgName          := "RCWA",
Version          := "1.0",
Date             := "24/02/2003",
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
                         HTMLStart := "doc/chap0.html",
                         PDFFile   := "doc/manual.pdf",
                         SixFile   := "doc/manual.six",
                         LongTitle := "[R]esidue [C]lass-[W]ise [A]ffine representations of groups",
                         Autoload  := false
                       ),
Dependencies     := rec(
                         GAP                    := ">=4.3",
                         NeededOtherPackages    := [ ["ResClasses", ">=1.0"], ["GRAPE",">=4.0"],
                                                     ["GAPDoc",">=0.99"] ],
                         SuggestedOtherPackages := [ ],
                         ExternalConditions     := [ ]
                       ),
AvailabilityTest := ReturnTrue,
BannerString     := Concatenation( "\nLoading RCWA ", ~.Version,
                                   " ([R]esidue [C]lass-[W]ise [A]ffine mappings and groups)",
                                   "\nby Stefan Kohl, kohl@mathematik.uni-stuttgart.de\n\n" ),
Autoload         := false,
TestFile         := "tst/testall.g",
Keywords         := [ "infinite permutation groups", "permutation groups over rings" ]

) );

####################################################################################################
##
#E  PkgInfo.g  . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
