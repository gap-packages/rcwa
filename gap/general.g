#############################################################################
##
#W  general.g                 GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains some more general pieces of code which are not direct-
##  ly related to RCWA. Some of them might perhaps later be moved into the
##  GAP Library or elsewhere.
##
Revision.general_g :=
  "@(#)$Id$";

#############################################################################
##
#M  \*( <n>, infinity ) . . . . . . . . . . for positive integer and infinity
#M  \*( infinity, <n> ) . . . . . . . . . . for infinity and positive integer
#M  \*( infinity, infinity )  . . . . . . . . . . . for infinity and infinity
##
##  In GAP 4.4.7, the GAP Library function `DirectProduct' and the general
##  method for `DirectProductOp' run into error if one of the factors is
##  known to be infinite. The methods below are installed as a workaround.
##  As maybe there are further similar places where finiteness is assumed
##  implicitly, it may be good if these methods remain available after 4.4.8.
##
InstallMethod( \*, "for positive integer and infinity (RCWA)",
               ReturnTrue, [ IsPosInt, IsInfinity ], 0,
               function ( n, infty ) return infinity; end );
InstallMethod( \*, "for infinity and positive integer (RCWA)",
               ReturnTrue, [ IsInfinity, IsPosInt ], 0,
               function ( infty, n ) return infinity; end );
InstallMethod( \*, "for infinity and infinity (RCWA)",
               ReturnTrue, [ IsInfinity, IsInfinity ], 0,
               function ( infty1, infty2 ) return infinity; end );

#############################################################################
##
#F  SearchCycle( <l> ) . . . a utility function for detecting cycles in lists
##
DeclareGlobalFunction( "SearchCycle" );
InstallGlobalFunction( SearchCycle,

  function ( l )

    local  pos, incr, refine;

    if Length(l) < 2 then return fail; fi;
    pos := 1; incr := 1;
    while Length(Set(List([1..Int((Length(l)-pos+1)/incr)],
                          i->l{[pos+(i-1)*incr..pos+i*incr-1]}))) > 1 do
      pos := pos + 1; incr := incr + 1;
      if pos + 2*incr-1 > Length(l) then return fail; fi;
    od;
    refine := SearchCycle(l{[pos..pos+incr-1]});
    if refine <> fail then return refine;
                      else return l{[pos..pos+incr-1]}; fi;
  end );

#############################################################################
##
#O  AllProducts( <D>, <k> ) . . all products of <k>-tuples of elements of <D>
#M  AllProducts( <l>, <k> ) . . . . . . . . . . . . . . . . . . . . for lists
##
DeclareOperation( "AllProducts", [ IsListOrCollection, IsPosInt ] );
InstallMethod( AllProducts,
               "for lists (RCWA)", ReturnTrue, [ IsList, IsPosInt ], 0,
               function ( l, k ) return List(Tuples(l,k),Product); end );

#############################################################################
##
#O  GeneratorsAndInverses( <D> ) list of generators of <D> and their inverses
#M  GeneratorsAndInverses( <G> ) . . . . . . . . . . . . . . . . . for groups
##
DeclareOperation( "GeneratorsAndInverses", [ IsMagmaWithInverses ] );
InstallMethod( GeneratorsAndInverses,
               "for groups (RCWA)", true, [ IsGroup ], 0,
               G -> Concatenation(GeneratorsOfGroup(G),
                                  List(GeneratorsOfGroup(G),g->g^-1)) );

#############################################################################
##
#F  EpimorphismByGenerators( <D1>, <D2> ) .  epi.: gen's of <F>->gen's of <G>
#O  EpimorphismByGeneratorsNC( <D1>, <D2> ) .  NC version as underlying oper.
#M  EpimorphismByGeneratorsNC( <G>, <H> ) . . . . . . . . . . . .  for groups
##
DeclareOperation( "EpimorphismByGeneratorsNC", [ IsDomain, IsDomain ] );
InstallMethod( EpimorphismByGeneratorsNC,
               "for groups (RCWA)", ReturnTrue, [ IsGroup, IsGroup ], 0,
  function ( G, H )
    return GroupHomomorphismByImagesNC(G,H,GeneratorsOfGroup(G),
                                           GeneratorsOfGroup(H));
  end );
DeclareGlobalFunction( "EpimorphismByGenerators" );
InstallGlobalFunction( EpimorphismByGenerators,
  function ( D1, D2 )
    return EpimorphismByGeneratorsNC(D1,D2);
  end );

#############################################################################
##
#M  IsCyclic( <G> ) . . . . . . . . . . . . . . . . default method for groups
##
InstallMethod( IsCyclic, "default method for groups (RCWA)", true,
               [ IsGroup ], 50,

  function ( G )
    if   HasIsFinitelyGeneratedGroup(G) and not IsFinitelyGeneratedGroup(G)
    then return false; fi;
    if   HasGeneratorsOfGroup(G) and Length(GeneratorsOfGroup(G)) = 1
    then return true;
    else TryNextMethod(); fi;
  end );

#############################################################################
##
#M  AbelianInvariants( <G> ) . .  for groups knowing an iso. to a pcp group
#M  AbelianInvariants( <G> ) . .  for groups knowing an iso. to a perm.-group
##
InstallMethod( AbelianInvariants,
               "for groups knowing an isomorphism to a pcp group", true,
               [ IsGroup and HasIsomorphismPcpGroup ], 0,
               G -> AbelianInvariants(Image(IsomorphismPcpGroup(G))) );
InstallMethod( AbelianInvariants,
               "for groups knowing an isomorphism to a permutation group",
               true, [ IsGroup and HasIsomorphismPermGroup ], 0,
               G -> AbelianInvariants(Image(IsomorphismPermGroup(G))) );

#############################################################################
##
#F  SaveAsBitmapPicture( <picture>, <filename>, <colored> )
##
##  Writes the pixel matrix <picture> to a bitmap- (bmp-) picture file
##  named <filename>. The argument <colored> is a boolean which specifies
##  whether a 24-bit True-Color picture file or a monochrome picture file
##  should be created. In the former case, <picture> must be an integer
##  matrix, with entries n = 65536*red+256*green+blue in the range 0..2^24-1
##  giving the RGB values of the colors of the pixels. In the latter case,
##  <picture> is a GF(2) matrix, where zeros stand for black pixels and
##  ones stand for white pixels.
##
DeclareGlobalFunction( "SaveAsBitmapPicture" );
InstallGlobalFunction( SaveAsBitmapPicture,

  function ( picture, filename, colored )

    local  AppendHex, AppendWidthHeight, str,
           height, width, vec8, pix, x, y, i;

    AppendHex := function ( hexstr )
      Append(str,List([1..Length(hexstr)/2],
                      i->CHAR_INT(IntHexString(hexstr{[2*i-1,2*i]}))));
    end;

    AppendWidthHeight := function ()
      Add(str,CHAR_INT(width mod 256));  Add(str,CHAR_INT(Int(width/256)));
      Add(str,CHAR_INT(0));              Add(str,CHAR_INT(0));
      Add(str,CHAR_INT(height mod 256)); Add(str,CHAR_INT(Int(height/256)));
    end;

    if not IsMatrix(picture) or not IsString(filename)
      or not colored in [ true, false ]
    then
      Error("usage: SavePicture( <picture>, <filename>, <colored> )\n");
    fi;

    width := Length(picture[1]);   height := Length(picture);
    width := width - width mod 32; height := height - height mod 32;
    str := "";
    if colored then
      AppendHex("424D36EE0200000000003600000028000000"); AppendWidthHeight();
      AppendHex("0000010018000000000000EE020013");
      AppendHex("0B0000130B00000000000000000000");
      for y in [1..height] do
        for x in [1..width] do
          pix := picture[y][x];
          Add(str,CHAR_INT(pix mod 256)); pix := Int(pix/256);
          Add(str,CHAR_INT(pix mod 256)); pix := Int(pix/256);
          Add(str,CHAR_INT(pix));
        od;
      od;
    else # b/w picture
      AppendHex("424D3E7D0000000000003E00000028000000"); AppendWidthHeight();
      AppendHex("00000100010000000000007D0000CE0E0000C4");
      AppendHex("0E0000000000000000000000000000FFFFFF00");
      vec8 := List([0..255],i->CoefficientsQadic(i+256,2){[8,7..1]})*Z(2)^0;
      for i in [1..256] do ConvertToGF2VectorRep(vec8[i]); od;
      for y in [1..height] do
        for x in [1,9..width-7] do
          Add(str,CHAR_INT(Position(vec8,picture[y]{[x..x+7]})-1));
        od;
      od;
    fi;
    if   filename[Length(filename) - 3] <> '.'
    then filename := Concatenation(filename,".BMP"); fi;
    FileString(filename,str);
  end );

#############################################################################
##
#E  general.g . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here