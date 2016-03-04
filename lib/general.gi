#############################################################################
##
#W  general.gi                 GAP4 Package `RCWA'                Stefan Kohl
##
##  This file contains some more general pieces of code which are not direct-
##  ly related to RCWA. Some of them might perhaps later be moved into the
##  GAP Library or elsewhere.
##
#############################################################################

#############################################################################
##
#M  EquivalenceClasses( <list>, <relation> )
#M  EquivalenceClasses( <list>, <classinvariant> )
##
##  Returns a list of equivalence classes on <list> under <relation>
##  or a list of equivalence classes on <list> given by <classinvariant>,
##  respectively.
##
##  The argument <relation> must be a function which takes as arguments
##  two entries of <list> and returns either true or false, and which
##  describes an equivalence relation on <list>.
##  The argument <classinvariant> must be a function which takes as argument
##  an element of <list> and returns a class invariant.
##  
InstallOtherMethod( EquivalenceClasses,
                    "for a list and a relation or a class invariant (RCWA)",
                    ReturnTrue, [ IsList, IsFunction ], 0,

  function ( list, relation )

    local  classes, invs, longestfirst, byinvs, elm, pos, inserted, count;

    if IsEmpty(list) then return []; fi;

    longestfirst := function(c1,c2) return Length(c1) > Length(c2); end;
    byinvs := function(c1,c2) return relation(c1[1]) < relation(c2[1]); end;

    if   NumberArgumentsFunction(relation) = 1 then
      invs    := List(list,relation);
      classes := List(Set(invs),inv->list{Positions(invs,inv)});
      Sort(classes,byinvs);
    elif NumberArgumentsFunction(relation) = 2 then
      classes := [[list[1]]]; count := 0;
      for elm in list{[2..Length(list)]} do
        inserted := false; count := count + 1;
        for pos in [1..Length(classes)] do
          if relation(elm,classes[pos][1]) then
            Add(classes[pos],elm);
            inserted := true;
            break;
          fi;
        od;
        if   not inserted
        then classes := Concatenation(classes,[[elm]]); fi;
        if   count mod 100 = 0 # rough performance heuristics ...
        then Sort(classes,longestfirst); fi;
      od;
      Sort(classes,longestfirst);
    else TryNextMethod(); fi;

    return classes;
  end );

#############################################################################
##
#S  The general trivial methods for `Trajectory'. ///////////////////////////
##
#############################################################################

#############################################################################
##
#M  Trajectory( <f>, <n>, <length> )
##
InstallOtherMethod( Trajectory,
                    "for function, starting point and length (RCWA)",
                    ReturnTrue, [ IsFunction, IsObject, IsPosInt ], 0,

  function ( f, n, length )

    local  l, i;

    l := [n];
    for i in [2..length] do
      n := f(n);
      Add(l,n);
    od;
    return l;
  end );

#############################################################################
##
#M  Trajectory( <f>, <n>, <terminal> )
##
InstallOtherMethod( Trajectory,
                    "for function, starting point and terminal set (RCWA)",
                    ReturnTrue, [ IsFunction, IsObject, IsListOrCollection ],
                    0,

  function ( f, n, terminal )

    local  l, i;

    l := [n];
    while not n in terminal do
      n := f(n);
      Add(l,n);
    od;
    return l;
  end );

#############################################################################
##
#M  Trajectory( <f>, <n>, <halt> )
##
InstallOtherMethod( Trajectory,
                 "for function, starting point and halting criterion (RCWA)",
                 ReturnTrue, [ IsFunction, IsObject, IsFunction ],
                 0,

  function ( f, n, halt )

    local  l, i;

    l := [n];
    while not halt(n) do
      n := f(n);
      Add(l,n);
    od;
    return l;
  end );

#############################################################################
##
#S  Multiplication with infinity. ///////////////////////////////////////////
##
#############################################################################

#############################################################################
##
#M  \*( <n>, infinity ) . . . . . . . . .  for positive rational and infinity
#M  \*( infinity, <n> ) . . . . . . . . .  for infinity and positive rational
#M  \*( infinity, infinity )  . . . . . . . . . . . for infinity and infinity
##
InstallMethod( \*, "for positive rational and infinity (RCWA)",
               ReturnTrue, [ IsPosRat, IsInfinity ], 0,
               function ( n, infty ) return infinity; end );
InstallMethod( \*, "for infinity and positive rational (RCWA)",
               ReturnTrue, [ IsInfinity, IsPosRat ], 0,
               function ( infty, n ) return infinity; end );
InstallMethod( \*, "for infinity and infinity (RCWA)",
               ReturnTrue, [ IsInfinity, IsInfinity ], 0,
               function ( infty1, infty2 ) return infinity; end );

#############################################################################
##
#S  Functions to generate small graphs. /////////////////////////////////////
##
#############################################################################

#############################################################################
##
#F  AllGraphs( <n> ) . . . .  all graphs with <n> vertices, up to isomorphism
##
InstallGlobalFunction( AllGraphs,

  function ( n )
    if not IsPosInt(n) then return fail; fi;
    return List(GraphClasses(n),Representative);
  end );

#############################################################################
##
#F  GraphClasses( <n> )  isomorphism classes of graphs with vertices 1,2,..,n
##
InstallGlobalFunction( GraphClasses,

  function ( n )

    local  classes;

    if not IsPosInt(n) then return fail; fi;
    classes := ShallowCopy(Orbits(SymmetricGroup(n),
                                  Combinations(Combinations([1..n],2)),
                                  function(Gamma,g)
                                    return Set(Gamma,k->OnSets(k,g));
                                  end));
    SortParallel(List(classes,cl->Length(cl[1])),classes);
    return classes;
  end );

#############################################################################
##
#F  IdGraph( <graph>, <classes> ) . identify the isomorphism class of <graph>
##
InstallGlobalFunction( IdGraph,

  function ( graph, classes )

    local  vertexnums, i;

    vertexnums := Set(Flat(graph));
    graph      := Set(graph,edge->List(edge,v->Position(vertexnums,v)));
    return First([1..Length(classes)],
                 i ->    Length(graph) = Length(classes[i][1])
                     and graph in classes[i]);
  end );

#############################################################################
##
#S  Some utilities for groups, group elements and homomorphisms. ////////////
##
#############################################################################

#############################################################################
##
#M  AbelianInvariants( <G> ) . .  for groups knowing an iso. to a pcp group
#M  AbelianInvariants( <G> ) . .  for groups knowing an iso. to a perm.-group
##
InstallMethod( AbelianInvariants,
               "for groups knowing an isomorphism to a pcp group", true,
               [ IsGroup and HasIsomorphismPcpGroup ], 0,
  function ( G )
    if IsPcpGroup(G) then TryNextMethod(); fi; # avoid recursion
    return AbelianInvariants(Image(IsomorphismPcpGroup(G)));
  end );

InstallMethod( AbelianInvariants,
               "for groups knowing an isomorphism to a permutation group",
               true, [ IsGroup and HasIsomorphismPermGroup ], 0,
  function ( G )
    if IsPermGroup(G) then TryNextMethod(); fi; # avoid recursion
    return AbelianInvariants(Image(IsomorphismPermGroup(G)));
  end );

#############################################################################
##
#F  ReducedWordByOrdersOfGenerators( <w>, <gensords> )
##
InstallGlobalFunction(  ReducedWordByOrdersOfGenerators,

  function ( w, gensords )

    local  ext, fam, i;

    fam := FamilyObj(w);
    ext := ShallowCopy(ExtRepOfObj(w));
    for i in [1,3..Length(ext)-1] do
      if gensords[ext[i]] < infinity then
        ext[i+1] := ext[i+1] mod gensords[ext[i]];
        if   ext[i+1] > gensords[ext[i]]/2
        then ext[i+1] := ext[i+1] - gensords[ext[i]]; fi;
      fi;
    od;
    return ObjByExtRep(fam,ext);
  end );

#############################################################################
##
#M  NormalizedRelator( <w>, <gensords> )
##
InstallMethod( NormalizedRelator,
               "for a word and a list of orders of generators", ReturnTrue,
               [ IsAssocWord, IsList ], 0,

  function ( w, gensords )

    local  c, old, twice, words, min, max, start, i, j;

    c := ShallowCopy(ExtRepOfObj(w));
    repeat
      old := ShallowCopy(c);
      for i in [2,4..Length(c)] do
        if   gensords[c[i-1]] < infinity
        then c[i] := c[i] mod gensords[c[i-1]]; fi;
      od;
      c := ShallowCopy(ExtRepOfObj(ObjByExtRep(FamilyObj(w),c)));
      if c = [] then return One(w); fi;
      min   := Minimum(c{[1,3..Length(c)-1]});
      start := Filtered([1,3..Length(c)-1],i->c[i]=min);
      max   := Maximum(c{start+1});
      start := Filtered(start,i->c[i+1]=max);
      twice := Concatenation(c,c);
      words := List(start,i->twice{[i..i+Length(c)-1]});
      SortParallel(List(words,v->[v{[1,3..Length(v)-1]},
                                  v{[2,4..Length(v)]}]),words);
      c := words[1];
    until c = old;
    w := ObjByExtRep(FamilyObj(w),c);
    return w;
  end );

#############################################################################
##
#M  AssignGeneratorVariables( <G> ) . .  for rcwa groups with at most 6 gen's
##
##  This method assigns the generators of <G> to global variables a, b, ... .
##
InstallMethod( AssignGeneratorVariables,
               "for rcwa groups with at most 6 generators (RCWA)",
               true, [ IsRcwaGroup ], 0,

  function ( G )

    local  gens, names, name, i;

    gens := GeneratorsOfGroup(G);
    if Length(gens) > 6 then TryNextMethod(); fi;
    names := "abcdef";
    for i in [1..Length(gens)] do
      name := names{[i]};
      if IsBoundGlobal(name) then
        if   IsReadOnlyGlobal(name)
        then Error("variable ",name," is read-only"); fi;
        UnbindGlobal(name);
        Info(InfoWarning,1,"The global variable ",name,
                           " has been overwritten.");
      fi;
      BindGlobal(name,gens[i]);
      MakeReadWriteGlobal(name);
    od;
    Print("The following global variables have been assigned: ");
    for i in [1..Length(gens)] do
      Print(names{[i]});
      if i < Length(gens) then Print(", "); fi;
    od;
    Print("\n");
  end );

#############################################################################
##
#S  The code for loading and saving bitmap images. //////////////////////////
##
#############################################################################

#############################################################################
##
#F  SaveAsBitmapPicture( <picture>, <filename> ) . . . .  save bitmap picture
##
InstallGlobalFunction( SaveAsBitmapPicture,

  function ( picture, filename )

    local  AppendHex, Append16Bit, Append32Bit, str, colored,
           height, width, fullwidth, length, offset, vec8, pix,
           chunk, fill, x, y, n, i;

    Append16Bit := function ( n )
      Add(str,CHAR_INT(n mod 256)); Add(str,CHAR_INT(Int(n/256)));
    end;

    Append32Bit := function ( n )
      Add(str,CHAR_INT(n mod 256)); n := Int(n/256);
      Add(str,CHAR_INT(n mod 256)); n := Int(n/256);
      Add(str,CHAR_INT(n mod 256)); n := Int(n/256);
      Add(str,CHAR_INT(n));
    end;

    if not IsMatrix(picture) or not IsString(filename)
      or (not IsInt(picture[1][1]) and not picture[1][1] in GF(2))
    then Error("usage: SaveAsBitmapPicture( <picture>, <filename> )\n"); fi;

    colored := IsInt(picture[1][1]);
    height  := Length(picture);
    width   := Length(picture[1]);
    if colored then fullwidth := width + (width mod 4)/3;
    elif width mod 32 <> 0 then
      fullwidth := width + 32 - width mod 32;
      fill := List([1..fullwidth-width],i->Zero(GF(2)));
      ConvertToGF2VectorRep(fill);
      picture := List(picture,line->Concatenation(line,fill));
    else fullwidth := width; fi;
    str := "BM";
    if colored then offset := 54; length := 3 * fullwidth * height + offset;
               else offset := 62; length := (fullwidth * height)/8 + offset;
    fi;
    for n in [length,0,offset,40,width,height] do Append32Bit(n); od;
    Append16Bit(1);
    if colored then
      Append16Bit(24);
      for i in [1..6] do Append32Bit(0); od;
      for y in [1..height] do
        for x in [1..width] do
          pix := picture[y][x];
          Add(str,CHAR_INT(pix mod 256)); pix := Int(pix/256);
          Add(str,CHAR_INT(pix mod 256)); pix := Int(pix/256);
          Add(str,CHAR_INT(pix));
        od;
        for i in [1..width mod 4] do Add(str,CHAR_INT(0)); od;
      od;
    else # monochrome picture
      Append16Bit(1);
      for i in [1..6] do Append32Bit(0); od;
      Append32Bit(0); Append32Bit(2^24-1);
      vec8 := List([0..255],i->CoefficientsQadic(i+256,2){[8,7..1]})*Z(2)^0;
      for i in [1..256] do ConvertToGF2VectorRep(vec8[i]); od;
      for y in [1..height] do
        for x in [1,9..fullwidth-7] do
          Add(str,CHAR_INT(PositionSorted(vec8,picture[y]{[x..x+7]})-1));
        od;
      od;
    fi;
    FileString(filename,str);
  end );

#############################################################################
##
#F  LoadBitmapPicture( <filename> ) . . . . . . . . . . . load bitmap picture
##
InstallGlobalFunction( LoadBitmapPicture,

  function ( filename )

    local  str, picture, height, width, fullwidth, vec8, chunk, x, y, i;

    if   not IsString(filename)
    then Error("usage: LoadBitmapPicture( <filename> )\n"); fi;

    str    := StringFile(filename);
    if str = fail then Error("file not found"); return fail; fi;
    width  := List(str{[19..22]},INT_CHAR) * List([0..3],i->256^i);
    height := List(str{[23..26]},INT_CHAR) * List([0..3],i->256^i);
    if INT_CHAR(str[29]) = 24 then # 24-bit RGB picture
      fullwidth := width + (width mod 4)/3;
      picture := List([1..height],
                      y->List([1..Int(fullwidth)],
                              x->List(str{[55+3*(fullwidth*(y-1)+x-1)..
                                           55+3*(fullwidth*(y-1)+x-1)+2]},
                                      INT_CHAR)
                                *[1,256,65536]));
    else # monochrome picture
      if width mod 32 = 0 then fullwidth := width;
                          else fullwidth := width + 32 - width mod 32; fi;
      vec8 := List([0..255],i->CoefficientsQadic(i+256,2){[8,7..1]})*Z(2)^0;
      for i in [1..256] do ConvertToGF2VectorRep(vec8[i]); od;
      picture := List([1..height],y->Concatenation(List([1,9..fullwidth-7],
                     x->vec8[INT_CHAR(str[63+(fullwidth*(y-1)+x-1)/8])+1])));
    fi;
    if width = fullwidth then return picture;
                         else return picture{[1..height]}{[1..width]}; fi;
  end );

#############################################################################
##
#S  Routines for drawing or modifying bitmap images. ////////////////////////
##
#############################################################################

#############################################################################
##
#F  DrawGrid( <U>, <range_y>, <range_x>, <filename> )
##
InstallGlobalFunction( DrawGrid,

  function ( U, range_y, range_x, filename )

    local  grid, x, y, one, offset_x, offset_y, colors, color, pos;

    if   not (   IsResidueClassUnionOfZxZ(U)
              or IsList(U) and ForAll(U,IsResidueClassUnionOfZxZ))
      or not IsRange(range_y) or not IsRange(range_x)
      or not IsString(filename)
    then
      Error("usage: DrawGrid( <U>, <range_y>, <range_x>, <filename> )\n");
      return fail;
    fi;

    offset_x := -Minimum(range_x) + 1;
    offset_y := -Minimum(range_y) + 1;

    if IsResidueClassUnionOfZxZ(U) then

      grid     := NullMat(Length(range_y),Length(range_x),GF(2));
      one      := One(GF(2));

      for y in range_y do for x in range_x do
        if not [y,x] in U then grid[y+offset_y][x+offset_x] := one; fi;
      od; od;

    else

      colors := [[255,0,0],[0,255,0],[0,0,255],[255,255,0],[255,0,255],
                 [0,255,255],[255,128,128],[128,255,128],[128,128,255]]
              * [65536,256,1];

      grid := NullMat(Length(range_y),Length(range_x));

      for y in range_y do
        for x in range_x do
          pos := First([1..Length(U)],k->[y,x] in U[k]);
          if   pos = fail then color := 0;
          elif pos > Length(colors) then color := 2^24-1;
          else color := colors[pos]; fi;
          grid[y+offset_y][x+offset_x] := color;
        od;
      od;

    fi;

    SaveAsBitmapPicture( grid, filename );

  end );

#############################################################################
##
#E  general.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
