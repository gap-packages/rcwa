####################################################################################################
##
##  PackageInfo.g                         GAP4 Package `RCWA'                            Stefan Kohl
##  
#H  @(#)$Id$
##

SetPackageInfo( rec(

PackageName      := "RCWA",
Subtitle         := "Residue Class-Wise Affine Mappings and Groups",
Version          := "0.0",
Date             := "11/06/2004",
ArchiveURL       := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa/rcwa-0.0",
ArchiveFormats   := ".tar.gz",
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
PackageInfoURL   := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa/PackageInfo.g",
AbstractHTML     := "This package deals with some kind of infinite permutation groups over rings.",
PackageWWWHome   := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa.html",
PackageDoc       := rec(
                         BookName  := "RCWA",
                         ArchiveURLSubset := ["doc"],
                         HTMLStart := "doc/chap0.html",
                         PDFFile   := "doc/manual.pdf",
                         SixFile   := "doc/manual.six",
                         LongTitle := "[R]esidue [C]lass-[W]ise [A]ffine representations of groups",
                         Autoload  := false
                       ),
Dependencies     := rec(
                         GAP                    := ">=4.4",
                         NeededOtherPackages    := [ ["ResClasses", ">=2.0"], ["GRAPE",">=4.0"],
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
#E  PackageInfo.g  . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
