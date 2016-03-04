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
#S  Operations to construct new mappings from given ones. ///////////////////
##
#############################################################################

#############################################################################
##
#O  PiecewiseMapping( <sources>, <maps> )
##
##  Returns the mapping f composed from the mappings <maps> defined on
##  <sources>. Here, <sources> and and <maps> must be lists of the same
##  length, and for any i, <maps>[i] must be defined on <sources>[i] or
##  on a superset thereof.
##
DeclareOperation( "PiecewiseMapping", [ IsList, IsList ] );

#############################################################################
##
#S  Functions to generate and identify small graphs. ////////////////////////
##
#############################################################################

#############################################################################
##
#F  AllGraphs( <n> ) . . . .  all graphs with <n> vertices, up to isomorphism
##
##  This function returns a list of all graphs with vertices 1, 2, ... , <n>,
##  up to isomorphism. The graphs are represented as lists of edges.
##
DeclareGlobalFunction( "AllGraphs" );

#############################################################################
##
#F  GraphClasses( <n> )  isomorphism classes of graphs with vertices 1,2,..,n
##
##  This function returns a list of isomorphism classes of graphs with
##  vertices 1, 2, ... , <n>, where the graphs are represented as lists of
##  edges.
##
DeclareGlobalFunction( "GraphClasses" );

#############################################################################
##
#F  IdGraph( <graph>, <classes> ) . identify the isomorphism class of <graph>
##
##  Finds the index i such that <graph> lies in the i-th class in the list
##  <classes>. The graph <graph> needs to be represented as a list of edges,
##  and <classes> needs to have the same format as the return value of
##  GraphClasses( n ) for some positive integer n. If the list <classes>
##  contains no class which contains <graph>, then the function returns fail.
##
DeclareGlobalFunction( "IdGraph" );

#############################################################################
##
#S  Some utilities for groups, group elements and homomorphisms. ////////////
##
#############################################################################

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
#F  DrawGrid( <U>, <range_y>, <range_x>, <filename> )
##
##  Draws a picture of the residue class union <U> of Z^2 or the partition
##  <U> of Z^2 into residue class unions, respectively.
##
DeclareGlobalFunction( "DrawGrid" );

#############################################################################
##
#E  general.gd . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
