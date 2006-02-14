
                              The RCWA Package
                              ================


                                  Abstract

RCWA is a  GAP 4  package which provides methods  for investigating [R]esidue
[C]lass-[W]ise [A]ffine groups by means of computation.

Residue class-wise affine groups are  permutation groups  acting on the inte-
gers, whose elements are bijective residue class-wise affine mappings.  Typi-
cally they are infinite.

A mapping  f: Z -> Z  is called residue class-wise affine if there is a posi-
tive integer m such that the restrictions of f to the residue classes (mod m)
are all affine.  This means that for any residue class r(m) in Z/mZ there are
coefficients  a_r(m), b_r(m), c_r(m)  in  Z  such that the restriction of the
mapping f to the set r(m) = {r + km | k in Z} is given by

                                        a_r(m) * n + b_r(m)
           f|_r(m):  r(m) -> Z,  n |->  -------------------.
                                              c_r(m)

Residue class-wise affine groups are countable.   "Many" of them act multiply
transitively on  Z  or on subsets thereof.  Only relatively basic facts about
their structure are known so far. This package is intended to serve as a tool
for obtaining a better understanding of their rich and interesting group
theoretical and combinatorial structure.

Residue class-wise affine groups can be generalized in a natural way to  euc-
lidean rings other than the integers. While this package undoubtedly provides
most functionality for residue class-wise affine groups over the integers, at
least rudimentarily  it also covers the cases  that the  underlying ring is a
semilocalization of  Z  or a polynomial ring  in  one variable over  a finite
field.

The original motivation for  investigating  residue class-wise affine  groups
comes from the famous 3n+1 Conjecture,  which is an assertion about a surjec-
tive, but not injective residue class-wise affine mapping.

Residue class-wise affine  groups  are  introduced  in  the  author's  thesis
'Restklassenweise affine Gruppen'.   A copy of  this thesis  and  an  english
translation thereof are distributed with this package (see thesis/thesis.pdf,
thesis/thesis_e.pdf).   It is officially published  at  the following  sites:

         http://deposit.ddb.de/cgi-bin/dokserv?idn=977164071
         (Archivserver Deutsche Bibliothek)

         http://elib.uni-stuttgart.de/opus/volltexte/2005/2448/
         (OPUS-Datenbank Universität Stuttgart).


                                Requirements

The RCWA package needs at least  GAP 4.4.6,  ResClasses 2.2.0,  GRAPE 4.0 and
GAPDoc 0.999.  It can be used under UNIX, under Windows and on the MacIntosh.
RCWA  is completely written in the  GAP language and does neither contain nor
require external binaries.  In particular,  warnings concerning missing bina-
ries when GRAPE is loaded can savely be ignored.


                                Installation

Like any other GAP package,  RCWA must be installed in the pkg/  subdirectory
of the GAP distribution.  This is accomplished by extracting the distribution
file in this directory.   When you have done this you can load the package as
usual via LoadPackage( "rcwa" );.

For further advice  on questions of technical nature  please see the  chapter
`Auxiliary functions' in the manual.

                                    ---

If you have problems with this package, wish to make comments or suggestions,
or if you find bugs, please send e-mail to

Stefan Kohl, kohl@mathematik.uni-stuttgart.de

