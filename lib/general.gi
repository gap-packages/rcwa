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
#S  Some utility functions for lists and records. ///////////////////////////
##
#############################################################################

#############################################################################
##
#F  SearchCycle( <list> ) .  a utility function for detecting cycles in lists
##
InstallGlobalFunction( SearchCycle,

  function ( list )

    local  preperiod, cycle, startpos, mainpart, mainpartdiffs,
           elms, inds, min, n, d, i, j;

    n        := Length(list);
    mainpart := list{[Int(n/3)..n]};
    elms     := Set(mainpart);
    cycle    := [elms[1]];
    startpos := Filtered(Positions(list,elms[1]),i->i>n/3);
    if Length(elms) = 1 then
      if ValueOption("alsopreperiod") <> true then return cycle; else
        i := Length(list);
        repeat i := i - 1; until i = 0 or list[i] <> elms[1];
        preperiod := list{[1..i]};
        return [preperiod,cycle];
      fi;
    fi;
    i := 0;
    repeat
      i := i + 1;
      inds := Intersection(startpos+i,[1..n]);
      if inds = [] then return fail; fi;
      min := Minimum(list{inds});
      Add(cycle,min);
      startpos := Filtered(startpos,j->j+i<=n and list[j+i]=min);
      if Length(startpos) <= 1 then return fail; fi;
      mainpartdiffs := DifferencesList(Intersection(startpos,[Int(n/3)..n]));
      if mainpartdiffs = [] then return fail; fi;
      d := Maximum(mainpartdiffs); 
    until Length(cycle) = d;
    if    Minimum(startpos) > n/2
       or n-Maximum(startpos)-d+1 > d
       or list{[Maximum(startpos)+d..n]}<>cycle{[1..n-Maximum(startpos)-d+1]}
    then return fail; fi;
    if ValueOption("alsopreperiod") <> true then return cycle; else
      i := Minimum(startpos) + Length(cycle);
      repeat
        i := i - Length(cycle);
      until i <= 0 or list{[i..i+Length(cycle)-1]} <> cycle;
      preperiod := list{[1..i+Length(cycle)-1]};
      return [preperiod,cycle];
    fi;
  end );

#############################################################################
##
#F  AssignGlobals( <record> )
##
##  This auxiliary function assigns the record components of <record>
##  to global variables with the same names.
##
InstallGlobalFunction( AssignGlobals,

  function ( record )

    local  names, name;

    names := RecNames(record);
    for name in names do
      if IsBoundGlobal(name) then
        if IsReadOnlyGlobal(name)
        then
          MakeReadWriteGlobal(name);
          Info(InfoWarning,1,"The read-only global variable ",name,
                             " has been overwritten.");
        else
          Info(InfoRCWA,1,"The global variable ",name,
                          " has been overwritten.");
        fi;
        UnbindGlobal(name);
      fi;
      BindGlobal(name,record.(name));
      MakeReadWriteGlobal(name);
    od;
    Print("The following global variables have been assigned:\n",
          Set(names),"\n");
  end );

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
#S  Some utilities for integers and combinatorics. //////////////////////////
##
#############################################################################

#############################################################################
##
#F  AllSmoothIntegers( <maxp>, <maxn> )
#F  AllSmoothIntegers( <primes>, <maxn> )
##
InstallGlobalFunction( AllSmoothIntegers,

  function ( maxp, maxn )

    local  extend, nums, primes, p;

    extend := function ( n, mini )

      local  i;

      if n > maxn then return; fi;
      Add(nums,n);
      for i in [mini..Length(primes)] do
        extend(primes[i]*n,i);
      od;
    end;

    if   IsInt(maxp)
    then primes := Filtered([2..maxp],IsPrimeInt);
    elif IsList(maxp) and ForAll(maxp,p->IsInt(p) and IsPrimeInt(p))
    then primes := maxp;
    else return fail; fi;
    if not IsPosInt(maxn) then return fail; fi;

    nums := [];
    extend(1,1);
    return Set(nums);
  end );

#############################################################################
##
#F  ExponentOfPrime( <n>, <p> )
##
InstallGlobalFunction( ExponentOfPrime,

  function ( n, p )

    local  k;

    if IsZero(p) then return fail; fi;
    if IsZero(n) then return infinity; fi;
    k := 0;
    while IsZero(n mod p) do n := n/p; k := k + 1; od;
    return k;
  end );

#############################################################################
##
#F  NextProbablyPrimeInt( <n> ) . . next integer passing `IsProbablyPrimeInt'
##
InstallGlobalFunction( NextProbablyPrimeInt,

  function ( n )
    if   -3 = n            then n := -2;
    elif -3 < n  and n < 2 then n :=  2;
    elif n mod 2 = 0       then n := n+1;
    else                        n := n+2;
    fi;
    while not IsProbablyPrimeInt(n) do
        if n mod 6 = 1 then n := n+4;
        else                n := n+2;
        fi;
    od;
    return n;
  end );

#############################################################################
##
#F  RestrictedPartitionsWithoutRepetitions( <n>, <S> )
##
##  Given a positive integer n and a set of positive integers S, this func-
##  tion returns a list of all partitions of n into distinct elements of S.
##  The only difference to `RestrictedPartitions' is that no repetitions are
##  allowed.
##
InstallGlobalFunction( RestrictedPartitionsWithoutRepetitions,

  function ( n, S )

    local  look, comps;

    look := function ( comp, remaining_n, remaining_S )

      local  newcomp, newremaining_n, newremaining_S, part, l;

      l := Reversed(remaining_S);
      for part in l do
        newcomp        := Concatenation(comp,[part]);
        newremaining_n := remaining_n - part;
        if newremaining_n = 0 then Add(comps,newcomp);
        else
          newremaining_S := Set(Filtered(remaining_S,
                                         s->s<part and s<=newremaining_n));
          if newremaining_S <> [] then
            look(newcomp,newremaining_n,newremaining_S);
          fi;
        fi;
      od;
    end;

    comps := [];
    look([],n,S);
    return comps;
  end );

#############################################################################
##
#S  Iterator for the prime numbers. \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
##
#############################################################################

BindGlobal( "PrimeNumbersIterator_next",

  function ( iter )

    local  sieve, range, p, q, pos, endpos, maxdiv_old, maxdiv, i, j;

    if iter!.index = 0 then
      sieve := ListWithIdenticalEntries(iter!.chunksize,0);
      if iter!.n = 0 then sieve[1] := 1; fi;
      for i in [1..iter!.nrdivs] do
        p := iter!.offset[i][1];
        if p > iter!.n then pos := 2 * p;
                       else pos := iter!.offset[i][2]; fi;
        if pos = 0 then pos := p; fi;
        endpos := pos + Int((iter!.chunksize-pos)/p) * p;
        if pos <= iter!.chunksize then
          range := [pos,pos+p..endpos];
          if IsRangeRep(range) then
            ADD_TO_LIST_ENTRIES_PLIST_RANGE(sieve,range,1);
          else
            for j in range do sieve[j] := sieve[j] + 1; od;
          fi;
        fi;
        if endpos <= iter!.chunksize then
          iter!.offset[i][2] := endpos + p - iter!.chunksize;
        else
          iter!.offset[i][2] := iter!.offset[i][2] - iter!.chunksize;
        fi;
      od;
      iter!.primepos := Positions(sieve,0);
    fi;
    iter!.index := iter!.index + 1;
    p           := iter!.n + iter!.primepos[iter!.index];
    iter!.p     := p;
    iter!.pi    := iter!.pi + 1;
    if iter!.index = Length(iter!.primepos) then
      iter!.index  := 0;
      iter!.n      := iter!.n + iter!.chunksize;
      maxdiv_old   := iter!.maxdiv;
      iter!.maxdiv := RootInt(iter!.n + iter!.chunksize);
      for q in Filtered([maxdiv_old+1..iter!.maxdiv],IsPrimeInt) do
        Add(iter!.offset,[q,(q-iter!.n) mod q]);
      od;
      iter!.nrdivs := Length(iter!.offset);
    fi;
    return p;
  end );

BindGlobal( "PrimeNumbersIterator_copy",

  function ( iter )

    return rec( chunksize      := iter!.chunksize,
                n              := iter!.n,
                p              := iter!.p,
                pi             := iter!.pi,
                index          := iter!.index,
                primepos       := ShallowCopy(iter!.primepos),
                nrdivs         := iter!.nrdivs,
                maxdiv         := iter!.maxdiv,
                offset         := StructuralCopy(iter!.offset) );
  end );

#############################################################################
##
#F  PrimeNumbersIterator(  )
#F  PrimeNumbersIterator( chunksize )
##
InstallGlobalFunction( PrimeNumbersIterator,

  function ( arg )

    local  next, copy, chunksize, maxdiv, nrdivs, offset;

    if   Length(arg) >= 1 and IsPosInt(arg[1])
    then chunksize := Maximum(arg[1],100); # must be bigger than largest
    else chunksize := 10000000; fi;        # prime gap in range looped over

    maxdiv     := RootInt(chunksize);
    offset     := List(Filtered([2..maxdiv],IsPrimeInt),p->[p,0]);
    nrdivs     := Length(offset);

    return IteratorByFunctions( 
             rec( NextIterator   := PrimeNumbersIterator_next,
                  IsDoneIterator := ReturnFalse,
                  ShallowCopy    := PrimeNumbersIterator_copy,
                  chunksize      := chunksize,
                  n              := 0,
                  p              := 0,
                  pi             := 0,
                  index          := 0,
                  primepos       := [],
                  nrdivs         := nrdivs,
                  maxdiv         := maxdiv,
                  offset         := offset ) );
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
#F  ListOfPowers( <g>, <exp> ) . . . . . .  list of powers <g>^1 .. <g>^<exp>
##
InstallGlobalFunction(  ListOfPowers,

  function ( g, exp )

    local  powers, n;

    powers := [g];
    for n in [2..exp] do Add(powers,powers[n-1]*g); od;
    return powers;
  end );

#############################################################################
##
#M  GeneratorsAndInverses( <G> ) . . . . . . . . . . . . . . . . . for groups
##
InstallMethod( GeneratorsAndInverses,
               "for groups (RCWA)", true, [ IsGroup ], 0,
               G -> Concatenation(GeneratorsOfGroup(G),
                                  List(GeneratorsOfGroup(G),g->g^-1)) );

#############################################################################
##
#F  EpimorphismByGenerators( <D1>, <D2> ) .  epi.: gen's of <F>->gen's of <G>
#M  EpimorphismByGeneratorsNC( <D1>, <D2> ) .  NC version as underlying oper.
#M  EpimorphismByGeneratorsNC( <G>, <H> ) . . . . . . . . . . . .  for groups
##
InstallMethod( EpimorphismByGeneratorsNC,
               "for groups (RCWA)", ReturnTrue, [ IsGroup, IsGroup ], 0,
  function ( G, H )
    return GroupHomomorphismByImagesNC(G,H,GeneratorsOfGroup(G),
                                           GeneratorsOfGroup(H));
  end );
InstallGlobalFunction( EpimorphismByGenerators,
  function ( D1, D2 )
    return EpimorphismByGeneratorsNC(D1,D2);
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
    for i in [1..Length(gens)] do Print(names{[i]},", "); od;
    Print("\n");
  end );

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
#S  Some utilities related to output or conversion to strings. //////////////
##
#############################################################################

#############################################################################
##
#F  LaTeXStringFactorsInt( <n> ) . . . . prime factorization in LaTeX format
##
InstallGlobalFunction( LaTeXStringFactorsInt,

  function ( n )

    local  facts, str, i; 

    if   not IsInt(n)
    then Error("usage: LaTeXStringFactorsInt( <n> ) for an integer <n>"); fi;

    if n < 0 then str := "-"; n := -n; else str := ""; fi;
    facts := Collected(Factors(n));
    for i in [1..Length(facts)] do
      Append(str,String(facts[i][1]));
      if facts[i][2] > 1 then
        Append(str,"^");
        if facts[i][2] >= 10 then Append(str,"{"); fi;
        Append(str,String(facts[i][2]));
        if facts[i][2] >= 10 then Append(str,"}"); fi;
      fi;
      if i < Length(facts) then Append(str," \\cdot "); fi;
    od;
    return str;
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
#S  Utility to convert GAP logfiles to XHTML 1.0 Strict. ////////////////////
##
#############################################################################

#############################################################################
##
#F  Log2HTML( logfilename ) . . . . . convert GAP logfile to XHTML 1.0 Strict
##
InstallGlobalFunction( Log2HTML,

  function ( logfilename )

    local  outputname, s1, s2, header, footer, pos,
           lastlf, nextlf, crlf, prompt;

    if ARCH_IS_UNIX() then crlf := 1; else crlf := 2; fi;
    header := Concatenation(
                "<?xml version = \"1.0\" encoding = \"ISO-8859-1\"?>\n\n",
                "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"\n",
                "                      \"http://www.w3.org/TR/xhtml1/DTD/",
                "xhtml1-strict.dtd\">\n<html>\n\n<head>\n  <title> ",
                logfilename, " </title>\n  <link rel = \"stylesheet\" ",
                "type = \"text/css\" href = \"gaplog.css\" />\n",
                "</head>\n\n<body>\n\n<pre class = \"logfile\">\n");
    footer := "</pre> </body> </html>";
    s1 := StringFile(logfilename);
    pos := PositionSublist(s1,"gap>"); prompt := "gap> ";
    s2 := ReplacedString(s1{[1..pos-1]},"<","&lt;");
    while pos <> fail do
      s2 := Concatenation(s2,"<em class = \"prompt\">",prompt,"</em>");
      s2 := Concatenation(s2,"<em class = \"input\">");
      nextlf := Position(s1,'\n',pos); prompt := "gap>";
      if nextlf = fail then nextlf := Length(s1); fi;
      s2 := Concatenation(s2,ReplacedString(s1{[pos+5..nextlf-crlf]},
                                            "<","&lt;"),"</em>");
      while nextlf < Length(s1) and s1[nextlf+1] = '>' do
        s2 := Concatenation(s2,"\n<em class = \"prompt\">></em>",
                            "<em class = \"input\">");
        lastlf := nextlf;
        nextlf := Position(s1,'\n',lastlf);
        if nextlf = fail then nextlf := Length(s1); fi;
        s2 := Concatenation(s2,ReplacedString(s1{[lastlf+2..nextlf-crlf]},
                                              "<","&lt;"),"</em>");
      od;
      s2 := Concatenation(s2,"\n");
      pos := PositionSublist(s1,"\ngap>",nextlf-1);
      if pos = fail then pos := Length(s1); fi;
      if pos > nextlf then
        s2 := Concatenation(s2,"<em class = \"output\">",
                            ReplacedString(s1{[nextlf+1..pos-crlf]},
                                           "<","&lt;"),"</em>\n");
      fi;
      if pos > Length(s1) - 3 then break; fi;
    od;
    s2 := Concatenation(header,s2,footer);
    logfilename := LowercaseString(logfilename); 
    if   PositionSublist(logfilename,".log") <> fail
    then outputname := ReplacedString(logfilename,".log",".html");
    elif PositionSublist(logfilename,".txt") <> fail
    then outputname := ReplacedString(logfilename,".txt",".html");
    else outputname := Concatenation(logfilename,".html"); fi;
    FileString(outputname,s2);
  end );

#############################################################################
##
#E  general.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here