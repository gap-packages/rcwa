#############################################################################
##
#W  integral.tst               GAP4 Package `RCWA'                Stefan Kohl
##
#H  @(#)$Id$
##

gap> START_TEST("$Id$");
gap> oldformat := RESCLASSES_VIEWING_FORMAT;;
gap> oldwarninglevel := InfoLevel(InfoWarning);;
gap> SetInfoLevel(InfoWarning,0);
gap> ResidueClassUnionViewingFormat("short");
gap> IdentityIntegralRcwaMapping;
IdentityMapping( Integers )
gap> ZeroIntegralRcwaMapping;
ZeroMapping( Integers, Integers )
gap> Order(IdentityIntegralRcwaMapping);
1
gap> RcwaMapping(Integers,[[2,0,1]]);
Rcwa mapping of Z: n -> 2n
gap> RcwaMapping(Integers,1,[[2,0,1]]);
Rcwa mapping of Z: n -> 2n
gap> f := RcwaMapping((1,2,3)(8,9),[4..20]);
<rcwa mapping of Z with modulus 17>
gap> f * One(f) = f and One(f) * f = f;
true
gap> f * Zero(f) = Zero(f) and Zero(f) * f = Zero(f);
true
gap> Action(Group(f),[4..20]) = Group([(5,6)]);
true
gap> IsIdenticalObj(f!.coeffs,Coefficients(f));
true
gap> T := RcwaMapping([[1,0,2],[3,1,2]]);
<rcwa mapping of Z with modulus 2>
gap> Print(T,"\n");
RcwaMapping( [ [ 1, 0, 2 ], [ 3, 1, 2 ] ] )
gap> IsInjective(T);
false
gap> IsSurjective(T);
true
gap> Coefficients(T);
[ [ 1, 0, 2 ], [ 3, 1, 2 ] ]
gap> Display(T^3);

Surjective rcwa mapping of Z with modulus 8

                n mod 8                |                 n^f
---------------------------------------+--------------------------------------
  0                                    | n/8
  1                                    | (9n + 7)/8
  2                                    | (3n + 2)/8
  3                                    | (9n + 5)/8
  4                                    | (3n + 4)/8
  5                                    | (3n + 1)/8
  6                                    | (9n + 10)/8
  7                                    | (27n + 19)/8

gap> Length(Trajectory(RcwaMapping([[1,0,2],[5,-1,2]]),19,1,"stop"));
307
gap> A := ResidueClass(Integers,3,2);
2(3)
gap> Image(T,A);
1(3) U 8(9)
gap> PreImage(T,A);
1(2) U 4(6)
gap> B := ResidueClass(Integers,3,1);;
gap> M := Union(Difference(B,[1,4,10]),[2,5,14]);
1(3) U [ 2, 5, 14 ] \ [ 1, 4, 10 ]
gap> Display(Image(T,M));
 
The residue class 2 ( mod 3 ) of Z
 
and the elements
 
 1 7
 
without the elements
 
 2 5

gap> PreImage(T,M);
2(6) U [ 1, 3, 4, 9, 10, 28 ] \ [ 2, 8, 20 ]
gap> Display(last);
 
The residue class 2 ( mod 6 ) of Z
 
and the elements
 
  1  3  4  9 10 28
 
without the elements
 
  2  8 20

gap> t := RcwaMapping([[-1,0,1]]);
Rcwa mapping of Z: n -> -n
gap> Order(t);
2
gap> LaTeXObj(t);
"n \\ \\mapsto \\ -n"
gap> MovedPoints(t);
Z \ [ 0 ]
gap> k := RcwaMapping([[-4,-8,1]]);;
gap> IsBijective(k);
false
gap> Image(k);
0(4)
gap> C := Difference(Integers,Union(A,B));;
gap> Image(k,C);
4(12)
gap> k := RcwaMapping([[-2,0,1]]);
Rcwa mapping of Z: n -> -2n
gap> Display(k);
Rcwa mapping of Z: n -> -2n
gap> IsInjective(k);
true
gap> IsSurjective(k);
false
gap> k := RcwaMapping([[-2,0,1],[1,0,1]]);;
gap> IsInjective(k);
true
gap> IsSurjective(k);
false
gap> k := RcwaMapping([[-2,0,1],[-1,1,1]]);;
gap> IsSurjective(k);
false
gap> IsInjective(k);
false
gap> k := RcwaMapping([[2,3,1]]);
Rcwa mapping of Z: n -> 2n + 3
gap> Display(k);
Rcwa mapping of Z: n -> 2n + 3
gap> k := RcwaMapping([[-2,3,1]]);
Rcwa mapping of Z: n -> -2n + 3
gap> Display(k);
Rcwa mapping of Z: n -> -2n + 3
gap> k := RcwaMapping([[-1,3,1]]);
Rcwa mapping of Z: n -> -n + 3
gap> k := RcwaMapping([[-1,-3,1]]);
Rcwa mapping of Z: n -> -n - 3
gap> k := RcwaMapping([[2,0,1],[0,3,1]]);
<rcwa mapping of Z with modulus 2>
gap> PreImage(k,[0,1,4,8,14]);
[ 0, 2, 4 ]
gap> PreImage(k,[0,1,3,4,8,14]);
1(2) U [ 0, 2, 4 ]
gap> Display(last);
 
The residue class 1 ( mod 2 ) of Z
 
and the elements
 
 0 2 4

gap> ZeroOne := RcwaMapping([[0,0,1],[0,1,1]]);;
gap> PreImagesElm(ZeroOne,6);
[  ]
gap> PreImagesElm(ZeroOne,1);
1(2)
gap> Image(ZeroOne);
[ 0, 1 ]
gap> e1 := RcwaMapping([[1,4,1],[2,0,1],[1,0,2],[2,0,1]]);;
gap> S := Difference(Integers,[1,2,3]);;
gap> im := Image(e1,S);
Z \ [ 1, 2, 6 ]
gap> pre := PreImage(e1,im);
Z \ [ 1, 2, 3 ]
gap> u := RcwaMapping([[3,0,5],[9,1,5],[3,-1,5],[9,-2,5],[9,4,5]]);;
gap> IsBijective(u);
true
gap> Modulus(u);
5
gap> Display(u^-1);

Bijective rcwa mapping of Z with modulus 9

                n mod 9                |                 n^f
---------------------------------------+--------------------------------------
  0 3 6                                | 5n/3
  1 4 7                                | (5n + 1)/3
  2                                    | (5n - 1)/9
  5                                    | (5n + 2)/9
  8                                    | (5n - 4)/9

gap> Modulus(T^u);
18
gap> PrimeSet(T^(u^-1));
[ 2, 3, 5 ]
gap> Order(u);
infinity
gap> 15^T; 
23 
gap> PreImageElm(u,8);
4
gap> PreImagesElm(T,8);
[ 5, 16 ]
gap> PreImagesElm(ZeroIntegralRcwaMapping,0);
Integers
gap> d := RcwaMapping([[0,0,1],[0,1,1]]);;
gap> PreImagesRepresentative(d,1);
1
gap> G := RCWA(Integers);
RCWA(Z)
gap> Size(G);
infinity
gap> IsFinite(G);
false
gap> IsFinitelyGeneratedGroup(G);
false
gap> IsGroup(G);
true
gap> IsNaturalRCWA_Z(G);
true
gap> One(G);
IdentityMapping( Integers )
gap> Representative(G);
Rcwa mapping of Z: n -> -n
gap> IsSubgroup(RCWA(Integers),TrivialIntegralRcwaGroup);
true
gap> IsSimple(G);
false
gap> IsSolvable(G);
false
gap> IsPerfect(G);
false
gap> Centre(G);
Trivial rcwa group over Z
gap> u in G;
true
gap> t in G;
true
gap> T in G;
false
gap> if not IsBound(rc) then
>      rc := function(r,m) return ResidueClass(DefaultRing(m),m,r); end;
>    fi;
gap> a := RcwaMapping([[3,0,2],[3, 1,4],[3,0,2],[3,-1,4]]);;
gap> b := RcwaMapping([[3,0,2],[3,13,4],[3,0,2],[3,-1,4]]);;
gap> c := RcwaMapping([[3,0,2],[3, 1,4],[3,0,2],[3,11,4]]);;
gap> a = RcwaMapping([rc(0,2),rc(1,4),rc(3,4)],[rc(0,3),rc(1,3),rc(2,3)]);
true
gap> MovedPoints(a);
Z \ [ -1, 0, 1 ]
gap> cl := ResidueClass(Integers,3,1);
1(3)
gap> im := Image(a,cl);
1(9) U 5(9) U 6(9)
gap> PreImage(a,im);
1(3)
gap> pre := PreImage(a,cl);
1(4)
gap> PreImage(a,last);
6(8) U 1(16) U 7(16)
gap> Image(a,pre);
1(3)
gap> cl := ResidueClass(Integers,2,0);;
gap> Image(a,cl);
0(3)
gap> PreImage(a,cl);
0(4) U 3(8) U 5(8)
gap> Image(a,PreImage(a,cl)) = cl;
true
gap> PreImage(a,Image(a,cl)) = cl;
true
gap> cl := ResidueClass(Integers,5,3);;
gap> Image(a,PreImage(a,cl)) = cl;
true
gap> PreImage(a,Image(a,cl)) = cl;
true
gap> TrajectoryModulo(a,8,20) = TrajectoryModulo(a,8,4,20);
true
gap> TrajectoryModulo(a,8,10,100);
[ 8, 2, 8, 7, 0, 0, 5, 4, 1, 8, 7, 3, 2, 8, 2, 8, 2, 3, 2, 3, 5, 4, 1, 3, 0,
  5, 6, 9, 4, 6, 9, 7, 8, 2, 8, 2, 3, 0, 5, 9, 7, 0, 0, 5, 4, 6, 9, 4, 6, 4,
  6, 9, 7, 5, 1, 1, 1, 3, 2, 3, 2, 3, 7, 3, 5, 4, 1, 8, 7, 0, 5, 1, 8, 2, 3,
  5, 4, 1, 1, 6, 9, 9, 4, 1, 6, 4, 1, 8, 7, 5, 1, 3, 5, 4, 1, 6, 4, 6, 9, 2 ]
gap> ab := Comm(a,b);;
gap> ac := Comm(a,c);;
gap> bc := Comm(b,c);;
gap> Order(ab);
6
gap> Order(ac);
6
gap> Order(bc);
12
gap> Display(ab);

Bijective rcwa mapping of Z with modulus 18, of order 6

               n mod 18                |                 n^f
---------------------------------------+--------------------------------------
   0  2  3  8  9 11 12 17              | n
   1 10                                | 2n - 5
   4  7 13 16                          | n + 3
   5 14                                | 2n - 4
   6                                   | (n + 2)/2
  15                                   | (n - 5)/2

gap> Print(LaTeXObj(ab));
n \ \longmapsto \
\begin{cases}
  n               & \text{if} \ n \in 0(9) \cup 2(9) \cup 3(9) \cup 8(9), \\
  2n - 5          & \text{if} \ n \in 1(9), \\
  n + 3           & \text{if} \ n \in 4(9) \cup 7(9), \\
  2n - 4          & \text{if} \ n \in 5(9), \\
  \frac{n + 2}{2} & \text{if} \ n \in 6(18), \\
  \frac{n - 5}{2} & \text{if} \ n \in 15(18).
\end{cases}
gap> Print(LaTeXObj(a:Indentation:=2));
  n \ \longmapsto \
  \begin{cases}
    \frac{3n}{2}     & \text{if} \ n \in 0(2), \\
    \frac{3n + 1}{4} & \text{if} \ n \in 1(4), \\
    \frac{3n - 1}{4} & \text{if} \ n \in 3(4).
  \end{cases}
gap> Print(LaTeXObj(a:german));
n \ \longmapsto \
\begin{cases}
  \linfrac{3n}{2}     & \falls n \in 0(2), \\
  \afffrac{3n + 1}{4} & \falls n \in 1(4), \\
  \afffrac{3n - 1}{4} & \falls n \in 3(4).
\end{cases}
gap> OrbitsModulo(ab,9);
[ [ 0 ], [ 1, 4, 5, 6, 7 ], [ 2 ], [ 3 ], [ 8 ] ]
gap> G := Group(ab,ac);
<rcwa group over Z with 2 generators>
gap> Display(G);

Rcwa group over Z, generated by

[

Bijective rcwa mapping of Z with modulus 18, of order 6

               n mod 18                |                 n^f
---------------------------------------+--------------------------------------
   0  2  3  8  9 11 12 17              | n
   1 10                                | 2n - 5
   4  7 13 16                          | n + 3
   5 14                                | 2n - 4
   6                                   | (n + 2)/2
  15                                   | (n - 5)/2


Bijective rcwa mapping of Z with modulus 18, of order 6

               n mod 18                |                 n^f
---------------------------------------+--------------------------------------
   0  1  6  7  9 10 15 16              | n
   2  5 11 14                          | n + 3
   3                                   | (n + 1)/2
   4 13                                | 2n - 5
   8 17                                | 2n - 4
  12                                   | (n - 4)/2

]

gap> TrivialSubgroup(G);
Trivial rcwa group over Z
gap> orb := Orbit(G,1);
[ -15, -12, -7, -6, -5, -4, -3, -2, -1, 1 ]
gap> MovedPoints(G);
1(3) U 2(3) U 3(9) U 6(9)
gap> OrbitsModulo(G,9);
[ [ 0 ], [ 1, 2, 3, 4, 5, 6, 7, 8 ] ]
gap> H := Action(G,orb);;
gap> H = Group([(1,2,3,4,6,8),(3,5,7,6,9,10)]);
true
gap> Size(H);
3628800
gap> Size(G);
3628800
gap> Modulus(G);
18
gap> Order(a);
infinity
gap> Comm(a,t);
IdentityMapping( Integers )
gap> x := ab*ac*ab^2*ac^3;
<bijective rcwa mapping of Z with modulus 18>
gap> x in G;
true
gap> u in G;
false
gap> ShortOrbits(G,[-20..20],100) =
>    [[-51,-48,-42,-39,-25,-23,-22,-20,-19,-17], [-18], 
>     [-33,-30,-24,-21,-16,-14,-13,-11,-10,-8], 
>     [-15,-12,-7,-6,-5,-4,-3,-2,-1,1], [-9], [0], 
>     [2,3,4,5,6,7,8,10,12,15], [9], 
>     [11,13,14,16,17,19,21,24,30,33], [18], 
>     [20,22,23,25,26,28,39,42,48,51]];
true
gap> IsPerfect(Group(a,b));
false
gap> g := RcwaMapping([[2,2,1],[1, 4,1],[1,0,2],[2,2,1],[1,-4,1],[1,-2,1]]);;
gap> h := RcwaMapping([[2,2,1],[1,-2,1],[1,0,2],[2,2,1],[1,-1,1],[1, 1,1]]);;
gap> Order(g);
7
gap> Order(h);
12
gap> Order(Comm(g,h));
infinity
gap> h in G;
false
gap> std := StandardConjugate(g);
<bijective rcwa mapping of Z with modulus 7, of order 7>
gap> tostd := StandardizingConjugator(g);
<bijective rcwa mapping of Z with modulus 12>
gap> g^tostd = std;
true
gap> std := StandardConjugate(ab);
<bijective rcwa mapping of Z with modulus 7, of order 6>
gap> tostd := StandardizingConjugator(ab);
<bijective rcwa mapping of Z with modulus 36>
gap> ab^tostd = std;
true
gap> r := g^ab;
<bijective rcwa mapping of Z with modulus 36, of order 7>
gap> HasStandardConjugate(r) and HasStandardizingConjugator(r);
true
gap> r^StandardizingConjugator(r)/StandardConjugate(r);
IdentityMapping( Integers )
gap> k := RcwaMapping([[1,1,1],[1, 4,1],[1,1,1],[2,-2,1],
>                      [1,0,2],[1,-5,1],[1,1,1],[2,-2,1]]);;
gap> std := StandardConjugate(k);
<bijective rcwa mapping of Z with modulus 3, of order 3>
gap> tostd := StandardizingConjugator(k);
<bijective rcwa mapping of Z with modulus 16>
gap> k^tostd = std;
true
gap> v := RcwaMapping([[-1,2,1],[1,-1,1],[1,-1,1]]);;
gap> w := RcwaMapping([[-1,3,1],[1,-1,1],[1,-1,1],[1,-1,1]]);;
gap> k := RcwaMapping([[-1,2,1],[1,-1,1],[1,-1,1],[1,1,1],[1,-1,1]]);;
gap> std := StandardConjugate(k);
<tame bijective rcwa mapping of Z with modulus 5>
gap> tostd := StandardizingConjugator(k);
<bijective rcwa mapping of Z with modulus 5>
gap> k^tostd = std;
true
gap> Order(tostd);
6
gap> Image(k,ResidueClass(Integers,3,2));
1(15) U 9(15) U 10(15) U 12(15) U 13(15)
gap> PreImage(k,last);
2(3)
gap> PreImage(k,last);
0(15) U 6(15) U 9(15) U 12(15) U 13(15)
gap> PreImage(k,last);
1(15) U 5(15) U 7(15) U 8(15) U 14(15)
gap> Image(k,last);
0(15) U 6(15) U 9(15) U 12(15) U 13(15)
gap> cls := List([0..2],r->ResidueClass(Integers,3,r));
[ 0(3), 1(3), 2(3) ]
gap> Union(List(cls,cl->Image(k,cl)));
Integers
gap> cls := List([0..6],r->ResidueClass(Integers,7,r));;
gap> Union(List(cls,cl->Image(k,cl)));
Integers
gap> Union(List(cls,cl->Image(a,cl)));
Integers
gap> Union(List(cls,cl->Image(u,cl)));
Integers
gap> F := ResidueClassUnion(Integers,5,[1,2],[3,8],[-4,1]);;
gap> im := Image(a,Image(a,F));
<union of 18 residue classes (mod 45)> U [ 3, 18 ] \ [ -9, 1 ]
gap> pre := PreImage(a,PreImage(a,im));
1(5) U 2(5) U [ 3, 8 ] \ [ -4, 1 ]
gap> C7 := Group(g);; 
gap> orb := Orbit(C7,F);
[ 1(5) U 2(5) U [ 3, 8 ] \ [ -4, 1 ], <union of 12 residue classes (mod
    30)> U [ 4, 8 ] \ [ -2, 5 ], <union of 24 residue classes (mod 60)> U
    [ 0, 4 ] \ [ -6, 3 ], <union of 24 residue classes (mod 60)> U [ 0, 2 ] \
    [ -10, 8 ], <union of 24 residue classes (mod 60)> U [ 1, 2 ] \ [ -5, 4 ],
  <union of 24 residue classes (mod 60)> U [ 1, 5 ] \ [ -1, 0 ],
  <union of 12 residue classes (mod 30)> U [ 3, 5 ] \ [ -3, 2 ] ]
gap> Union(orb{[1,2]});
<union of 19 residue classes (mod 30)> U [ 3, 4, 8 ] \ [ -2, 5 ]
gap> Union(orb{[1,2,3]});
<union of 44 residue classes (mod 60)> U [ 0, 4, 8 ] \ [ -6 ]
gap> Union(orb{[1,2,3,4]});
<union of 25 residue classes (mod 30)> U [ 0, 4 ] \ [ -10 ]
gap> Union(orb{[1,2,3,4,5]});
<union of 28 residue classes (mod 30)> U [ 0 ] \ [ -5 ]
gap> Union(orb{[1,2,3,4,5,6]});
Z \ [ -1 ]
gap> Union(orb{[1,2,3,4,5,6,7]});
Integers
gap> z := RcwaMapping([[2,  1, 1],[1,  1,1],[2, -1,1],[2, -2,1],
>                      [1,  6, 2],[1,  1,1],[1, -6,2],[2,  5,1],
>                      [1,  6, 2],[1,  1,1],[1,  1,1],[2, -5,1],
>                      [1,  0, 1],[1, -4,1],[1,  0,1],[2,-10,1]]);;
gap> set := Image(a,PreImage(h,Image(z,F)));
<union of 576 residue classes (mod 1440)> U [ 12, 21 ] \ [ -2, 0 ]
gap> control := PreImage(z,Image(h,PreImage(a,set)));;
gap> control = F;
true
gap> nb := RcwaMapping([[3,2,2],[2,-2,3],[3,2,2],[1,0,1],[3,2,2],[1,0,1]]);;
gap> Difference(Integers,Image(nb));
2(12) U 6(12)
gap> pc := RcwaMapping([[3,2,2],[2,-2,3],[3,2,2],[1,0,1],[3,2,2],[0,2,1]]);;
gap> im := Image(pc);
1(3) U 3(6) U 0(12) U 8(12) U [ 2 ]
gap> Display(im);
 
The union of the residue classes r ( mod 12 ) of Z for r =
 
  0  1  3  4  7  8  9 10
 
and the element
 
 2

gap> PreImage(pc,Difference(im,[4]));
Z \ [ 2, 7 ]
gap> CompositionMapping(a,b) = b*a;
true
gap> CompositionMapping(g,h) = h*g;
true
gap> x := RcwaMapping([[ 16,  2,  1], [ 16, 18,  1],
>                      [  1, 16,  1], [ 16, 18,  1],
>                      [  1, 16,  1], [ 16, 18,  1],
>                      [  1, 16,  1], [ 16, 18,  1],
>                      [  1, 16,  1], [ 16, 18,  1],
>                      [  1, 16,  1], [ 16, 18,  1],
>                      [  1, 16,  1], [ 16, 18,  1],
>                      [  1, 16,  1], [ 16, 18,  1],
>                      [  1,  0, 16], [ 16, 18,  1],
>                      [  1,-14,  1], [ 16, 18,  1],
>                      [  1,-14,  1], [ 16, 18,  1],
>                      [  1,-14,  1], [ 16, 18,  1],
>                      [  1,-14,  1], [ 16, 18,  1],
>                      [  1,-14,  1], [ 16, 18,  1],
>                      [  1,-14,  1], [ 16, 18,  1],
>                      [  1,-14,  1], [  1,-31,  1]]);
<rcwa mapping of Z with modulus 32>
gap> Order(x);
257
gap> 1^x;
34
gap> Display(a + b);

Rcwa mapping of Z with modulus 4

                n mod 4                |                 n^f
---------------------------------------+--------------------------------------
  0 2                                  | 3n
  1                                    | (3n + 7)/2
  3                                    | (3n - 1)/2

gap> Display(a - b);

Rcwa mapping of Z with modulus 4

                n mod 4                |                 n^f
---------------------------------------+--------------------------------------
  0 2 3                                | 0
  1                                    | -3

gap> TransitionGraph(a,4) 
>  = rec( isGraph := true, order := 4, group := Group(()), 
>         schreierVector := [ -1, -2, -3, -4 ], 
>         adjacencies := [ [ 1, 3 ], [ 1, 2, 3, 4 ],
>                          [ 2, 4 ], [ 1, 2, 3, 4 ] ], 
>         representatives := [ 1, 2, 3, 4 ],
>         names := [ 1, 2, 3, 4 ] );
true
gap> a*(bc*f) = (a*bc)*f;
true
gap> h*(a*b) = (h*a)*b;
true
gap> u*(ac^-1*g) = (u*ac^-1)*g;
true
gap> u*g*(u*g)^-1 = IdentityIntegralRcwaMapping;
true
gap> a*(b+c) = a*b + a*c;
true
gap> g*(a+u) = g*a + g*u;
true
gap> h*(b-t) = h*b - h*t;
true
gap> List([0..7],i->Modulus(g^i));
[ 1, 6, 12, 12, 12, 12, 6, 1 ]
gap> List([0..3],i->Modulus(u^i));
[ 1, 5, 25, 125 ]
gap> s := RcwaMapping([[1,0,1],[1,1,1],[3,  6,1],
>                      [1,0,3],[1,1,1],[3,  6,1],
>                      [1,0,1],[1,1,1],[3,-21,1]]);;
gap> List([0..9],i->Modulus(s^i));
[ 1, 9, 9, 27, 27, 27, 27, 27, 27, 1 ]
gap> G := Group(a*b,u^f,Comm(a,b));
<rcwa group over Z with 3 generators>
gap> PrimeSet(G);
[ 2, 3, 5, 17 ]
gap> g1 := RcwaMapping((1,2),[1..2]);
<rcwa mapping of Z with modulus 2>
gap> g2 := RcwaMapping((1,2,3),[1..3]);
<rcwa mapping of Z with modulus 3>
gap> g3 := RcwaMapping((1,2,3,4,5),[1..5]);
<rcwa mapping of Z with modulus 5>
gap> G := Group(g1,g2);
<rcwa group over Z with 2 generators>
gap> H := NiceObject(G);
Group([ (1,6)(2,3)(4,5), (1,5,6)(2,3,4) ])
gap> phi := NiceMonomorphism(G);;
gap> IsBijective(phi);
true
gap> Size(Image(phi));
24
gap> phi = IsomorphismPermGroup(G);
true
gap> IdGroup(G);
[ 24, 12 ]
gap> G;
<rcwa group over Z with 2 generators, of isomorphism type [ 24, 12 ]>
gap> Modulus(G);
6
gap> A4 := DerivedSubgroup(G);
<rcwa group over Z with 3 generators, of size 12>
gap> IsBijective(IsomorphismGroups(AlternatingGroup(4),A4));
true
gap> H := RcwaGroupByPermGroup(Group((1,2),(3,4),(5,6),(7,8),
>                                    (1,3)(2,4),(1,3,5,7)(2,4,6,8)));
<rcwa group over Z with 6 generators>
gap> Size(H);
384
gap> IsSolvable(H);
true
gap> List(DerivedSeries(H),Size);
[ 384, 96, 32, 2, 1 ]
gap> Modulus(H);
8
gap> NrConjugacyClassesOfRCWAZOfOrder(2);
infinity
gap> NrConjugacyClassesOfRCWAZOfOrder(105);
218
gap> IsTame(T);
false
gap> IsTame(ab);
true
gap> IsTame(G);
true
gap> IsTame(Group(ab,ac));
true
gap> nu := RcwaMapping([[1,1,1]]);
Rcwa mapping of Z: n -> n + 1
gap> IsTame(nu);
true
gap> IsTame(Group(nu));
true
gap> Size(Group(nu));
infinity
gap> x := RcwaMapping([[-1,2,1],[1,-1,1],[1,-1,1]]);
<rcwa mapping of Z with modulus 3>
gap> Order(x);
6
gap> List([-10..10],n->Length(Orbit(Group(x),n)));
[ 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 6, 6, 6, 6, 6, 6, 6, 6 ]
gap> y := RcwaMapping([[-1,3,1],[1,-1,1],[1,-1,1],[1,-1,1]]);
<rcwa mapping of Z with modulus 4>
gap> Order(y);
8
gap> List([-10..10],n->Length(Orbit(Group(y),n)));
[ 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 8 ]
gap> Order(x*y);
24
gap> Order(Comm(x,y));
20
gap> IsIntegral(f);
true
gap> IsIntegral(u);
false
gap> IsIntegral(T);
false
gap> IsIntegral(nu);
true
gap> IsIntegral(nu^a);
false
gap> IsIntegral((nu^a)^2);
true
gap> IsIntegral(Group(a,b));
false
gap> IsIntegral(Group(g));
false
gap> IsIntegral(t);
true
gap> IsIntegral(RcwaMapping([[2,0,1]]));
true
gap> IsIntegral(RcwaMapping([[2,0,1],[3,5,1]]));
true
gap> IsIntegral(RcwaMapping([[1,0,2],[3,5,1]]));
false
gap> IsBalanced(t);
true
gap> IsBalanced(a);
false
gap> IsBalanced(nu*nu^a);
true
gap> IsBalanced(ab);
true
gap> IsClassWiseOrderPreserving(u);
true
gap> IsClassWiseOrderPreserving(T);
true
gap> IsClassWiseOrderPreserving(t);
false
gap> IsClassWiseOrderPreserving(nu);
true
gap> IsClassWiseOrderPreserving(nu^RcwaMapping([[-1,0,1],[1,0,1]]));
false
gap> IsClassWiseOrderPreserving(Group(a,b));
true
gap> IsClassWiseOrderPreserving(G);
true
gap> IsClassWiseOrderPreserving(Group(t,g,h));
false
gap> y := RcwaMapping([[28,   0, 9], [ 7, -16, 9], [28,   7, 9],
>                      [28,  42, 9], [ 7,   8, 9], [ 7, -17, 9],
>                      [ 7,  12,18], [ 7,  -4, 9], [28, -35, 9],
>                      [28,   0, 9], [ 7, -16, 9], [28,   7, 9],
>                      [28,  42, 9], [ 7,   8, 9], [ 7, -17, 9],
>                      [ 7, -87,18], [ 7,  -4, 9], [28, -35, 9]]);;
gap> ab^y = RcwaMapping((1,2,3,4,5,6),[1..7]);
true
gap> ShortOrbits(Group(u),[-30..30],100) = 
>    [[-13,-8,-7,-5,-4,-3,-2], [-10,-6], [-1], [0], [1,2], [3,5],
>     [24,36,39,40,44,48,60,65,67,71,80,86,93,100,112, 
>      128,138,155,167,187,230,248,312,446,520,803,867,1445]];
true
gap> ShortCycles(u,2);
[ [ 0 ], [ -1 ], [ 1, 2 ], [ 3, 5 ], [ -10, -6 ] ]
gap> ShortCycles(a,1);
[ [ 0 ], [ 1 ], [ -1 ] ]
gap> ShortCycles(a,2);
[ [ 0 ], [ 1 ], [ -1 ], [ 2, 3 ], [ -3, -2 ] ]
gap> DeterminantMat(TransitionMatrix(T,13));
-1/256
gap> TransitionMatrix(T^3,11) = TransitionMatrix(T,11)^3;
true
gap> Display(TransitionMatrix(a,7));
[ [  1/2,    0,  1/4,    0,    0,  1/4,    0 ],
  [    0,  1/4,    0,    0,  1/4,  1/2,    0 ],
  [  1/4,    0,    0,  3/4,    0,    0,    0 ],
  [    0,  1/2,  1/4,    0,    0,    0,  1/4 ],
  [    0,  1/4,    0,    0,    0,  1/4,  1/2 ],
  [  1/4,    0,    0,    0,  3/4,    0,    0 ],
  [    0,    0,  1/2,  1/4,    0,    0,  1/4 ] ]
gap> Display(TransitionMatrix(ab,20)*One(GF(7)));
 2 2 . 1 . . . . . . . 2 . . . 4 4 . . .
 . 2 . . 1 . . . 2 . . . . . . . . 4 6 .
 4 . 4 . . 1 . . . . . . 2 . . . . . . 4
 . 4 4 2 . . 1 . . 2 . . . . . . . . . 2
 . . . 6 6 . . 1 . . . . . 2 . . . . . .
 2 . . . . 6 4 . 1 . 2 . . . . . . . . .
 . . . . 2 . 2 4 4 1 . . . . 2 . . . . .
 . 2 . . . . . 2 . 4 5 2 . . . . . . . .
 . . . . . 2 . . 2 . . 5 4 . . 2 . . . .
 . . 2 . . . . . . 2 . . 3 4 4 . . . . .
 . . . . . . 2 . . . 2 . . 1 . 4 6 . . .
 . . . 2 . . . . . . . 2 . 2 1 . . 4 4 .
 4 . . . . . . 2 . . . . 2 . . 1 . 2 . 4
 . 4 4 . 2 . . . . . . . . 2 2 . 1 . . .
 . . . 4 4 . . . 2 . . . . . 2 . . 1 2 .
 . . . . . 6 4 . . . . . . . . 4 . . 1 .
 . . . . . . . 4 4 2 . . . . . . 2 . . 3
 1 . . . . . 2 . . 4 4 . . . . . 2 2 . .
 2 1 . . . . . . . . 2 4 4 . . . . . 2 .
 . . 1 . . . . 2 . . . . . 4 4 . . 2 . 2
gap> sigma2 := RcwaMapping([[1, 0,1],[3,3,2],[1,0,1],
>                           [2, 0,1],[1,0,1],[1,0,1],
>                           [1,-3,3],[3,3,2],[1,0,1],
>                           [1, 0,1],[1,0,1],[1,0,1],
>                           [2, 0,1],[3,3,2],[1,0,1],
>                           [1, 0,1],[1,0,1],[1,0,1]]);;
gap> sigma1 := StandardConjugate(sigma2);;
gap> sigma := sigma1*sigma2;
<bijective rcwa mapping of Z with modulus 36>
gap> fact := FactorizationOnConnectedComponents(sigma,36);;
gap> List(fact,MovedPoints);
[ 33(36) U 34(36) U 35(36), 9(36) U 10(36) U 11(36),
  <union of 23 residue classes (mod 36)> \ [ -6, 3 ] ]
gap> CoefficientsOnTrajectory(T,27,1,"stop",false);
[ 36472996377170786403, 195820718533800070543, 1180591620717411303424 ]
gap> List(CoefficientsOnTrajectory(sigma,37,37,"stop",true),
>         c->(c[1]*37+c[2])/c[3]){[1..23]} = Cycle(sigma,37);
true
gap> CoefficientsOnTrajectory(a,8,10,"length",true);
[ [ 1, 0, 1 ], [ 3, 0, 2 ], [ 9, 0, 4 ], [ 27, 0, 8 ], [ 81, -8, 32 ], 
  [ 243, -24, 64 ], [ 729, -72, 128 ], [ 2187, -88, 512 ], 
  [ 6561, -264, 1024 ], [ 19683, -1816, 4096 ] ]
gap> G := Group(g,h);;
gap> P := RespectedPartition(G);
[ 0(12), 1(12), 3(12), 4(12), 5(12), 6(12), 7(12), 9(12), 10(12), 11(12),
  2(24), 8(24), 14(24), 20(24) ]
gap> phi := IsomorphismMatrixGroup(G);;
gap> phi = NiceMonomorphism(G);
true
gap> M := Image(phi);
<matrix group with 2 generators>
gap> M = NiceObject(G);
true
gap> H := ActionOnRespectedPartition(G);
Group([ (1,11,2,5,3,12,4)(6,13,7,10,8,14,9), (1,11,2,10)(3,12,4)(5,6,13,7)(8,
    14,9) ])
gap> Size(H);
322560
gap> D := DerivedSubgroup(H);;
gap> Size(D);
161280
gap> IsPerfect(D);
true
gap> RankOfKernelOfActionOnRespectedPartition(G);
6
gap> K := KernelOfActionOnRespectedPartition(G);
<rcwa group over Z with 6 generators>
gap> RankMat(KernelOfActionOnRespectedPartitionHNFMat(G));
6
gap> IsAbelian(K);
true
gap> g in G;
true
gap> g*h^3*g^-2*h in G;
true
gap> a in G;
false
gap> G := Group(ab,ac);
<rcwa group over Z with 2 generators>
gap> One(G) in G;
true
gap> ab in G;
true
gap> ac^-1 in G;
true
gap> ab*bc^2*ac^-3 in G;
true
gap> a in G;
false
gap> t in G;
false
gap> u in G;
false
gap> T in G;
false
gap> nu^a in G;
false
gap> g in G;
false
gap> G := Group(a,b);
<rcwa group over Z with 2 generators>
gap> a*b in G;
true
gap> u in G;
false
gap> S0 := ContractionCentre(T,100,1000);
[ -136, -91, -82, -68, -61, -55, -41, -37, -34, -25, -17, -10, -7, -5, -1, 0,
  1, 2 ]
gap> f1 := RcwaMapping([[2,0,1]]);
Rcwa mapping of Z: n -> 2n
gap> f2 := RcwaMapping([[2,1,1]]);
Rcwa mapping of Z: n -> 2n + 1
gap> a_1 := Restriction(a,f1);
<wild bijective rcwa mapping of Z with modulus 8>
gap> a_2 := Restriction(a,f2);
<wild bijective rcwa mapping of Z with modulus 8>
gap> G := Group(a_1,a_2);
<rcwa group over Z with 2 generators>
gap> IsAbelian(G);
true
gap> Set(FactorizationOnConnectedComponents(a_1*a_2,2)) = Set([a_1,a_2]);
true
gap> List([-2..2],k->Multpk(a,2,k));
[ 1(2), 0(2), [  ], [  ], [  ] ]
gap> List([-2..2],k->Multpk(a,3,k));
[ [  ], [  ], [  ], Integers, [  ] ]
gap> List([-2..2],k->Multpk(a,5,k));
[ [  ], [  ], Integers, [  ], [  ] ]
gap> rc := function(r,m) return ResidueClass(Integers,m,r); end;;
gap> md := f -> [Multiplier(f),Divisor(f)];;
gap> c1 := Restriction(a^-1,RcwaMapping([[2,0,1]]));;
gap> c2 := RcwaMapping([[1,0,2,],[2,1,1],[1,-1,1],[2,1,1]]);;
gap> md(Comm(c1,c2));
[ 4, 3 ]
gap> Order(RcwaMapping([[rc(1,2),rc(36,72)]]));
2
gap> f1 := RcwaMapping([[rc(0,4),rc(1,6)],[rc(2,4),rc(5,6)]]);
<rcwa mapping of Z with modulus 12>
gap> Cycle(f1,rc(0,4));
[ 0(4), 1(6) ]
gap> Cycle(f1,rc(5,6));
[ 5(6), 2(4) ]
gap> G := Restriction(Group(a,b),RcwaMapping([[5,3,1]]));
<rcwa group over Z with 2 generators>
gap> MovedPoints(G);
3(5) \ [ -2, 3 ]
gap> Divergence(g);
1
gap> Divergence(a);
1.06066
gap> Divergence(u);
1.15991
gap> G := Group(g,h);
<rcwa group over Z with 2 generators>
gap> IsTransitive(G,Integers);
true
gap> H := Restriction(G,RcwaMapping([[3,2,1]]));
<tame rcwa group over Z with 2 generators, of size infinity>
gap> MovedPoints(H);
2(3)
gap> IsTransitive(H,MovedPoints(H));
true
gap> G := Group(a,b);
<rcwa group over Z with 2 generators>
gap> IsTransitive(G,Integers);
false
gap> H := Restriction(G,RcwaMapping([[3,2,1]]));
<rcwa group over Z with 2 generators>
gap> IsTransitive(H,MovedPoints(H));
false
gap> SetName(g,"g"); SetName(h,"h");
gap> D := DirectProduct(Group(a,b),Group(g,h),Group(nu,t));
<rcwa group over Z with 6 generators>
gap> Projection(D,1);;
gap> Embedding(D,2);
[ g, h ] -> [ <bijective rcwa mapping of Z with modulus 18, of order 7>,
  <bijective rcwa mapping of Z with modulus 18, of order 12> ]
gap> G := Group(g,h);;
gap> IsSolvable(G);
false
gap> IsPerfect(G);
false
gap> IsPerfect(TrivialSubgroup(G));
true
gap> g1 := RcwaMapping([[1,0,1],[2,0,1],[1,0,2],[2,0,1]]);;
gap> g2 := RcwaMapping([[1,0,1],[2,4,1],[1,0,2],[2,4,1]]);;
gap> IsSolvable(Group(g1,g2));
true
gap> ImageDensity(T);
4/3
gap> ImageDensity(a);
1
gap> ImageDensity(u);
1
gap> ImageDensity(RcwaMapping([[2,0,1]]));
1/2
gap> f0 := RcwaMapping([[2,0,1]]);;
gap> f1 := RcwaMapping([[2,1,1]]);
Rcwa mapping of Z: n -> 2n + 1
gap> f0 := RcwaMapping([[2,0,1]]);
Rcwa mapping of Z: n -> 2n
gap> f1 := RcwaMapping([[2,1,1]]);
Rcwa mapping of Z: n -> 2n + 1
gap> f := Restriction(g,f0)*Restriction(h,f1);
<bijective rcwa mapping of Z with modulus 12>
gap> Order(f);
84
gap> RestrictedPerm(f,ResidueClass(Integers,2,0));
<rcwa mapping of Z with modulus 12>
gap> Order(last);
7
gap> RestrictedPerm(f,ResidueClass(Integers,2,1));
<rcwa mapping of Z with modulus 12>
gap> Order(last);
12
gap> P1 := [rc(0,2),rc(1,4),rc(3,4)];
[ 0(2), 1(4), 3(4) ]
gap> P2 := [rc(0,3),rc(1,3),rc(2,3)];
[ 0(3), 1(3), 2(3) ]
gap> elm := RepresentativeAction(RCWA(Integers),P1,P2);
<rcwa mapping of Z with modulus 4>
gap> P1^elm = P2;
true
gap> elmt := RepresentativeAction(RCWA(Integers),P1,P2:IsTame);
<tame rcwa mapping of Z with modulus 24>
gap> P1^elmt = P2;
true
gap> RCWAReadExamples();
gap> List([-2..2],k->Determinant(a^k));
[ 0, 0, 0, 0, 0 ]
gap> List([-2..2],k->Determinant(b^k));
[ -2, -1, 0, 1, 2 ]
gap> Determinant(a^g);
0
gap> Determinant(b^g);
1
gap> Determinant(b^u);
1
gap> Determinant(a^kappa);
0
gap> Determinant(b^kappa);
1
gap> Determinant(b^kappatilde);
1
gap> Determinant(b^2*b^kappatilde*g^-1);
3
gap> Determinant(sigma);
0
gap> Determinant(sigma*b^-1);
-1
gap> Determinant(sigma*b^-1*nu);
0
gap> Determinant(sigma*b^-1*nu^2);
1
gap> Determinant(PseudoRandom(Group(g,h)));
0
gap> Sign(nu);
-1
gap> Sign(nu^2);
1
gap> Sign(nu^3);
-1
gap> Sign(t);
-1
gap> Sign(nu^3*t);
1
gap> Sign(a);
1
gap> Sign(a*b);
-1
gap> Sign((a*b)^2);
1
gap> Sign(Comm(a,b));
1
gap> SetOnWhichMappingIsClassWiseOrderPreserving(T);
Integers
gap> SetOnWhichMappingIsClassWiseOrderPreserving(u);
Integers
gap> SetOnWhichMappingIsClassWiseOrderReversing(t);
Integers
gap> SetOnWhichMappingIsClassWiseOrderPreserving(t);
[  ]
gap> SetOnWhichMappingIsClassWiseConstant(RcwaMapping([[2,0,1],[0,4,1]]));
1(2)
gap> LargestSourcesOfAffineMappings(a);
[ 0(2), 1(4), 3(4) ]
gap> LargestSourcesOfAffineMappings(One(a)); 
[ Integers ]
gap> LargestSourcesOfAffineMappings(T);
[ 0(2), 1(2) ]
gap> LargestSourcesOfAffineMappings(kappa);
[ 2(4), 1(4) U 0(12), 3(12) U 7(12), 4(12), 8(12), 11(12) ]
gap> cl := ResidueClassWithFixedRepresentative(2,1);
[1/2]
gap> cl^T;
[2/3]
gap> last^T;
[1/3] U [8/9]
gap> last^T;
[2/3] U [2/9] U [4/9] U [26/27]
gap> last^T;
[1/3] U [1/9] U [2/9] U [8/9] U [13/27] U [17/27] U [20/27] U [80/81]
gap> AsOrdinaryUnionOfResidueClasses(last);
1(3) U 2(9) U 8(9)
gap> PreImagesSet(T,cl);
[3/4] U [2/12] U [6/12] U [10/12]
gap> AsOrdinaryUnionOfResidueClasses(last);
2(4) U 3(4)
gap> PreImagesSet(T,last2);
[1/8] U [7/8] U [4/24] U [6/24] U [12/24] U [14/24] U [20/24] U [22/24]
gap> DELTA(last);            
1/4
gap> PreImagesSet(T,last2);
<union of 16 residue classes with fixed rep's>
gap> DELTA(last);            
5/4
gap> AsOrdinaryUnionOfResidueClasses(last2);
<union of 8 residue classes (mod 16)>
gap> Residues(last);
[ 2, 8, 9, 11, 12, 13, 14, 15 ]
gap> DecreasingOn(T);
0(2)
gap> DecreasingOn(T^2);
0(2) U 1(4)
gap> DecreasingOn(T^3);
0(4) U 2(8) U 5(8)
gap> DecreasingOn(a);
1(2)
gap> DecreasingOn(a^2);
1(8) U 7(8)
gap> DecreasingOn(a^3);
<union of 8 residue classes (mod 16)>
gap> FactorizationIntoGenerators(ab);
[ ClassShift(7,9), ClassShift(1,9)^-1, ClassTransposition(1,9,4,9),
  ClassTransposition(1,9,7,9), ClassTransposition(6,18,15,18),
  ClassTransposition(5,9,15,18), ClassTransposition(4,9,15,18),
  ClassTransposition(5,9,6,18), ClassTransposition(4,9,6,18) ]
gap> Product(last) = ab;
true
gap> FactorizationIntoGenerators(Comm(g,h));
[ ClassShift(3,6)^2, ClassShift(2,3)^-2, ClassTransposition(0,6,3,6) ]
gap> Product(last) = Comm(g,h);
true
gap> FactorizationIntoGenerators(nu*nu^a);
[ ClassShift(5,6), ClassShift(4,6), ClassTransposition(0,6,1,6),
  ClassTransposition(0,6,5,6), ClassTransposition(0,6,3,6),
  ClassTransposition(0,6,4,6), ClassTransposition(0,6,2,6),
  ClassTransposition(2,3,3,6), ClassTransposition(1,3,3,6),
  ClassTransposition(2,3,0,6), ClassTransposition(1,3,0,6) ]
gap> List([t,nu,tau,nu^2,nu^-1,t*nu],FactorizationIntoGenerators);
[ [ ClassReflection(0,1) ], [ ClassShift(0,1) ],
  [ ClassTransposition(0,2,1,2) ], [ ClassShift(0,1)^2 ],
  [ ClassShift(0,1)^-1 ], [ ClassReflection(0,1), ClassShift(0,1) ] ]
gap> FactorizationIntoGenerators(g^ClassReflection(0,4));
[ ClassShift(8,12), ClassShift(3,6), ClassTransposition(1,6,5,6),
  ClassTransposition(1,6,3,6), ClassTransposition(0,12,10,12),
  ClassTransposition(0,12,6,12), ClassTransposition(0,12,8,12),
  ClassTransposition(10,12,16,24), ClassTransposition(8,12,16,24),
  ClassTransposition(10,12,4,24), ClassTransposition(8,12,4,24),
  ClassTransposition(1,6,4,12), ClassTransposition(1,6,2,12),
  ClassReflection(4,6), ClassReflection(2,24) ]
gap> FactorizationIntoGenerators((ClassShift(1,3)*ClassReflection(0,2))^a);
[ ClassShift(15,18), ClassTransposition(1,9,5,9),
  ClassTransposition(5,9,15,18), ClassTransposition(1,9,15,18),
  ClassTransposition(5,9,6,18), ClassTransposition(1,9,6,18),
  ClassReflection(0,3) ]
gap> SetInfoLevel(InfoWarning,oldwarninglevel);
gap> ResidueClassUnionViewingFormat(oldformat);
gap> STOP_TEST( "integral.tst", 4000000000 );

#############################################################################
##
#E  integral.tst . . . . . . . . . . . . . . . . . . . . . . . . .  ends here