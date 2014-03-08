#############################################################################
##
#W  general.gd                 GAP4 Package `RCWA'                Stefan Kohl
##
##  This file contains declarations of some more general functions, opera-
##  tions and attributes which are not directly related to RCWA. Some of them
##  might perhaps later be moved into the GAP Library or elsewhere.
##
#############################################################################

#############################################################################
##
#S  Some utility functions for lists and records. ///////////////////////////
##
#############################################################################

#############################################################################
##
#F  SearchCycle( <l> ) . . . a utility function for detecting cycles in lists
##
DeclareGlobalFunction( "SearchCycle" );

#############################################################################
##
#F  AssignGlobals( <record> )
##
##  This auxiliary function assigns the record components of <record> to
##  global variables with the same names.
##
DeclareGlobalFunction( "AssignGlobals" );

#############################################################################
##
#S  Some utilities for integers and combinatorics. //////////////////////////
##
#############################################################################

#############################################################################
##
#F  AllSmoothIntegers( <maxp>, <maxn> )
##
##  Returns the set of all integers in the range [1..<maxn>] which have only
##  prime divisors in the range [2..<maxp>].
##
DeclareGlobalFunction( "AllSmoothIntegers" );

#############################################################################
##
#F  ExponentOfPrime( <n>, <p> )
##
##  The exponent of the prime <p> in the prime factorization of <n>.
##
DeclareGlobalFunction( "ExponentOfPrime" );

#############################################################################
##
#O  AllProducts( <D>, <k> ) . . all products of <k>-tuples of elements of <D>
#M  AllProducts( <l>, <k> ) . . . . . . . . . . . . . . . . . . . . for lists
##
DeclareOperation( "AllProducts", [ IsListOrCollection, IsPosInt ] );

#############################################################################
##
#F  RestrictedPartitionsWithoutRepetitions( <n>, <S> )
##
##  Given a positive integer n and a set of positive integers S, this func-
##  tion returns a list of all partitions of n into distinct elements of S.
##  The only difference to `RestrictedPartitions' is that no repetitions are
##  allowed.
##
DeclareGlobalFunction( "RestrictedPartitionsWithoutRepetitions" );

#############################################################################
##
#S  Some utilities for groups, group elements and homomorphisms. ////////////
##
#############################################################################

#############################################################################
##
#F  ListOfPowers( <g>, <exp> ) . . . . . .  list of powers <g>^1 .. <g>^<exp>
##
DeclareGlobalFunction( "ListOfPowers" );

#############################################################################
##
#O  GeneratorsAndInverses( <D> ) list of generators of <D> and their inverses
#M  GeneratorsAndInverses( <G> ) . . . . . . . . . . . . . . . . . for groups
##
DeclareOperation( "GeneratorsAndInverses", [ IsMagmaWithInverses ] );

#############################################################################
##
#F  EpimorphismByGenerators( <D1>, <D2> ) .epi.: gen's of <D1>->gen's of <D2>
#O  EpimorphismByGeneratorsNC( <D1>, <D2> ) .  NC version as underlying oper.
#M  EpimorphismByGeneratorsNC( <G>, <H> ) . . . . . . . . . . . .  for groups
##
DeclareOperation( "EpimorphismByGeneratorsNC", [ IsDomain, IsDomain ] );
DeclareGlobalFunction( "EpimorphismByGenerators" );

#############################################################################
##
#F  ReducedWordByOrdersOfGenerators( <w>, <gensords> )
##
##  Given a word <w>, this function returns the word obtained from <w> by
##  reducing the exponents of powers of generators modulo their orders, as
##  specified in the list <gensords>.
##
DeclareGlobalFunction( "ReducedWordByOrdersOfGenerators" );

#############################################################################
##
#O  NormalizedRelator( <w>, <gensords> )
##
##  Given a word <w>, this operation returns its normal form obtained by
##
##    1. reducing the exponents of powers of generators modulo their orders,
##       as specified in the list <gensords>,
##    2. cyclic reduction and
##    3. cyclic conjugation to the lexicographically smallest such conjugate.
##
##  As the name of the operation suggests, the main purpose of this operation
##  is to get the relators in a finite presentation short and nice, and to be
##  able to spot and remove redundant relators in easy cases.
##
DeclareOperation( "NormalizedRelator", [ IsAssocWord, IsList ] );

#############################################################################
##
#S  Some utilities related to output or conversion to strings. //////////////
##
#############################################################################

#############################################################################
##
#F  LaTeXStringFactorsInt( <n> )
##
##  Returns the prime factorization of the integer <n> as a string in LaTeX
##  format.
##
DeclareGlobalFunction( "LaTeXStringFactorsInt" );

#############################################################################
##
#S  The functions for loading and saving bitmap images. /////////////////////
##
#############################################################################

#############################################################################
##
#F  SaveAsBitmapPicture( <picture>, <filename> )
##
##  Writes the pixel matrix <picture> to a bitmap- (bmp-) picture file
##  named <filename>. The filename should include the entire pathname.
##
##  The argument <picture> can be a GF(2) matrix, in which case a monochrome
##  picture file is generated. In this case, zeros stand for black pixels and
##  ones stand for white pixels.
##
##  The argument <picture> can also be an integer matrix, in which case
##  a 24-bit True Color picture file is generated. In this case, the entries
##  of the matrix are supposed to be integers n = 65536*red+256*green+blue in
##  the range 0,...,2^24-1 specifying the RGB values of the colors of the
##  pixels.
##
DeclareGlobalFunction( "SaveAsBitmapPicture" );

#############################################################################
##
#F  LoadBitmapPicture( <filename> )
##
##  Loads the bitmap picture file <filename> created by `SaveAsBitmapPicture'
##  back into GAP. The function returns the pixel matrix <picture>, as it has
##  been passed as first argument to `SaveAsBitmapPicture'.
##  The file <filename> must be an uncompressed monochrome
##  or 24-bit True Color bitmap file.
##
DeclareGlobalFunction( "LoadBitmapPicture" );

#############################################################################
##
#S  Routines for drawing or modifying bitmap images. ////////////////////////
##
#############################################################################

#############################################################################
##
#F  ShrinkMonochromePictureToGrayscalesPicture( <filename>, <factor> )
##
##  Creates a greyscale picture from a monochrome bitmap picture.
##  The greyscale picture is by a factor of <factor> smaller than the
##  provided monochrome picture, and the grey values of its pixels are
##  determined by the numbers of black pixels in the correspoding
##  <factor> * <factor> squares of the input picture.
##
DeclareGlobalFunction( "ShrinkMonochromePictureToGrayscalesPicture" );

#############################################################################
##
#F  DrawGrid( <U>, <range_y>, <range_x>, <filename> )
##
##  Draws a picture of the residue class union <U> of Z^2 or the partition
##  <U> of Z^2 into residue class unions, respectively.
##
DeclareGlobalFunction( "DrawGrid" );

#############################################################################
##
#S  Functions for steganography in bitmap images. ///////////////////////////
##
#############################################################################

#############################################################################
##
#F  EncryptIntoBitmapPicture( <picturefile>, <cleartextfile>, <passphrase> )
#F  DecryptFromBitmapPicture( <picturefile>, <cleartextfile>, <passphrase> )
##
##  The first function encrypts the contents of the textfile <cleartextfile>
##  into the image from the file named <picturefile>, using the passphrase
##  <passphrase>. The modified image is written to a file whose name is
##  derived from <picturefile> by appending the string "-out".
##
##  The second function decrypts an encoded text from the file named
##  <picturefile> using the passphrase <passphrase>, and writes the obtained
##  cleartext to a file named <cleartextfile>.
##
##  These steganographic utility functions are designed for security rather
##  than speed, and are intended to be used for texts of the order of
##  magnitude of what one would normally write into the body of an e-mail
##  -- encoding about 100kb into a picture of usual size should be still
##  convenient, while the functions are definitely not suitable for
##  encoding entire backups or the like.
##
##  Info messages on the progress of the encryption / decryption are given
##  at InfoLevel 2 of InfoRCWA. 
##
DeclareGlobalFunction( "EncryptIntoBitmapPicture");
DeclareGlobalFunction( "DecryptFromBitmapPicture");

#############################################################################
##
#S  Utility to run a demonstration in a talk. ///////////////////////////////
##
#############################################################################

#############################################################################
##
#F  RunDemonstration( <filename> ) . . . . . . . . . . .  run a demonstration
##
##  This is a function to run little demonstrations, for example in talks.
##  It is adapted from the function `Demonstration' in the file lib/demo.g
##  of the main GAP distribution. 
##
DeclareGlobalFunction( "RunDemonstration" );

#############################################################################
##
#S  Utility to convert GAP log files to XHTML 1.0 Strict. ///////////////////
##
#############################################################################

#############################################################################
##
#F  Log2HTML ( logfilename )
##
##  Utility to convert GAP log files to XHTML 1.0 Strict.
##
##  Usage:
##
##  - Issue Log2HTML( <logfilename> ). The extension of the input file must
##    be *.log. The name of the output file is the same as the one of the
##    input file except that the extension *.log is replaced by *.html.
##
##  - Adapt the style file rcwa/doc/gaplog.css to your taste.
##
DeclareGlobalFunction( "Log2HTML" );

#############################################################################
##
#S  Test utilities. /////////////////////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#F  ReadTestWithTimings( <filename> ) . . . read test file and return timings
#F  ReadTestCompareTimings( <filename> [,<timingsdir> [,<createreference> ]])
##
DeclareGlobalFunction( "ReadTestWithTimings" ); TEST_TIMINGS := [];
DeclareGlobalFunction( "ReadTestCompareRuntimes" );

#############################################################################
##
#E  general.g . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here