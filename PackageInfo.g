####################################################################################################
##
##  PackageInfo.g                         GAP4 Package `RCWA'                            Stefan Kohl
##
####################################################################################################

SetPackageInfo( rec(

PackageName      := "RCWA",
Subtitle         := "Residue-Class-Wise Affine Groups",
Version          := "4.6.1",
Date             := "18/12/2017",
ArchiveURL       := "https://stefan-kohl.github.io/rcwa/rcwa-4.6.1",
ArchiveFormats   := ".tar.gz", # "-win.zip" when providing text files with Windows line breaks
Persons          := [
                      rec( LastName      := "Kohl",
                           FirstNames    := "Stefan",
                           IsAuthor      := true,
                           IsMaintainer  := true,
                           Email         := "stefan@mcs.st-and.ac.uk",
                           WWWHome       := "https://stefan-kohl.github.io/"
                         )
                    ],
Status           := "accepted",
CommunicatedBy   := "Bettina Eick (Braunschweig)",
AcceptDate       := "04/2005",
PackageWWWHome   := "https://stefan-kohl.github.io/rcwa.html",
README_URL       := "https://stefan-kohl.github.io/rcwa/README.rcwa",
PackageInfoURL   := "https://stefan-kohl.github.io/rcwa/PackageInfo.g",
AbstractHTML     := Concatenation("This package provides implementations of algorithms and ",
                                  "methods for computation in certain infinite permutation groups.",
                                  " For an abstract, see ",
                                  "<a href = \"",~.PackageWWWHome,"\">here</a>."),
PackageDoc       := rec(
                         BookName         := "RCWA",
                         ArchiveURLSubset := ["doc"],
                         HTMLStart        := "doc/chap0.html",
                         PDFFile          := "doc/manual.pdf",
                         SixFile          := "doc/manual.six",
                         LongTitle        := "[R]esidue-[C]lass-[W]ise [A]ffine groups",
                         Autoload         := true
                       ),
Dependencies     := rec(
                         GAP                    := ">=4.8.7",
                         NeededOtherPackages    := [ ["ResClasses",">=4.7.0"], ["GRAPE",">=4.7"],
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
                                   "\n  by Stefan Kohl, stefan@mcs.st-and.ac.uk.",
                                   "\nSee ?RCWA:About for information about the package.\n\n" ),
TestFile         := "tst/testall.g",
Keywords         := [ "infinite permutation groups", "permutation groups over rings",
                      "combinatorial group theory", "residue-class-wise affine groups",
                      "residue-class-wise affine mappings",
                      "Collatz conjecture", "3n+1 conjecture" ]

) );

####################################################################################################
##
#E  PackageInfo.g  . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
