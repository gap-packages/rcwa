README file for `RCWA' package.

This package for GAP 4 (at least version 4.4) provides routines
for computations with [R]esidue [C]lass-[W]ise [A]ffine mappings
of the integers, of its semilocalizations as well as of univariate
polynomial rings over finite fields, hence it can be used for
computations in certain types of infinite permutation groups.

It is completely written in the GAP language and contains /
requires no external binaries.

Recent versions of the packages `ResClasses', `GRAPE' and `GAPDoc'
are needed.

The package `RCWA' must be installed in the pkg/ - subdirectory
of the GAP distribution.

After extracting the distribution file in the proper place,
you can load the package via LoadPackage( "rcwa" );

Then you can build the manual by issueing RCWABuildManual( );
(this works only under UNIX, but should not be necessary
unless you got the package from CVS, since the distribution file
already contains all files produced by this function).

For further advice on questions of technical nature please see
the chapter `Auxiliary functions' in the manual.

If you have problems with this package, wish to make comments
or suggestions, or if you find bugs, please send e-mail to

Stefan Kohl, kohl@mathematik.uni-stuttgart.de


