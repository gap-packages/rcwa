########################################################################################################################################################################
##
##  PkgInfo.g                                                              GAP4 Package `RCWA'                                                               Stefan Kohl
##  
#H  @(#)$Id$
##
##  Preliminary, not yet to be distributed !!!
##
##  None of the files on my webpage referred to from here is currently existing.
##

SetPackageInfo( rec(

PkgName          := "RCWA",
Version          := "1.0",
Date             := "10/06/2002",
ArchiveURL       := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa/rcwa-1.0",
ArchiveFormats   := ".zoo",
Persons          := [
                      rec( LastName      := "Kohl",
                           FirstNames    := "Stefan",
                           IsAuthor      := true,
                           IsMaintainer  := true,
                           Email         := "kohl@mathematik.uni-stuttgart.de",
                           WWWHome       := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/",
                           PostalAddress := "Stefan Kohl\nMathematisches Institut B, 2. Lehrstuhl\nPfaffenwaldring 57\nUniversität Stuttgart\n70550 Stuttgart\nGermany",
                           Place         := "Stuttgart / Germany",
                           Institution   := "University of Stuttgart"
                         )
                    ],
Status           := "under development",
CommunicatedBy   := "",
AcceptDate       := "",
README_URL       := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa/README.rcwa",
PkgInfoURL       := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa/PkgInfo.g",
AbstractHTML     := "This package deals with some kind of infinite permutation groups over rings.",
PackageWWWHome   := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa.html",
PackageDoc       := rec(
                         BookName  := "RCWA",
                         Archive   := "http://www.cip.mathematik.uni-stuttgart.de/~kohlsn/rcwa/rcwa-1.0doc-win.zip",
                         HTMLStart := "doc/manual.html",
                         PDFFile   := "doc/manual.pdf",
                         SixFile   := "doc/manual.six",
                         LongTitle := "[R]esidue [C]lass-[W]ise [A]ffine representations of groups",
                         AutoLoad  := false
                       ),
Dependencies     := rec(
                         GAP                    := ">=4.3",
                         NeededOtherPackages    := [ "GAPDoc" ],
                         SuggestedOtherPackages := [ "GRAPE" ],
                         ExternalConditions     := [ ]
                       ),
AvailabilityTest := ReturnTrue,
Autoload         := true,
TestFile         := "tst/testall.g",
Keywords         := [ "Infinite permutation groups", "Permutation groups over rings" ]

) );

########################################################################################################################################################################
##
#E  PkgInfo.g  . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
