#############################################################################
##
#W  examples.g                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains the rcwa mappings used in the examples in the manual
##  as well as a number of other interesting or illustrative examples.
##

#############################################################################
##
##  Some basic ``building blocks''.
##
nu  := ClassShift(Integers);
t   := ClassReflection(Integers);
tau := ClassTransposition(0,2,1,2);

#############################################################################
##
##  The Collatz mapping.
##
T := RcwaMapping([[1,0,2],[3,1,2]]); SetName(T,"T");

Tp := RcwaMapping([[1,0,2],[3, 1,2]]); SetName(Tp,"T+");
Tm := RcwaMapping([[1,0,2],[3,-1,2]]); SetName(Tm,"T-");

#############################################################################
##
##  Section 4.1: Factoring Collatz' permutation of the integers
##
Collatz := RcwaMapping([[2,0,3],[4,-1,3],[4,1,3]]);
SetName(Collatz,"Collatz");

#############################################################################
##
##  Section 4.2: An rcwa mapping which seems to be contracting, but very slow
##
##  The trajectory of 3224 under f6 has length 19949562.
##
f6 := RcwaMapping([[1,0,6],[5,1,6],[7,-2,6],[11,3,6],[11,-2,6],[11,-1,6]]);
SetName(f6,"f6");

# A mapping still having long, but less extreme trajectories:

T7 := RcwaMapping([[1,0,6],[7,1,2],[1,0,2],[1,0,3],[1,0,2],[7,1,2]]);
SetName(T7,"T7");

# Some other probably contracting mappings with divergence very close to 1.

f5 := RcwaMapping([[7,0,5],[7,-2,5],[3,-1,5],[3,1,5],[7,2,5]]);
f7 := RcwaMapping([[5,0,7],[9,-2,7],[9,3,7],
                           [5,-1,7],[5,1,7],
                           [9,-3,7],[9,2,7]]);
f9 := RcwaMapping([[ 5, 0,9],[16, 2,9],[10,-2,9],
                   [11, 3,9],[ 5,-2,9],[ 5, 2,9],
                   [11,-3,9],[10, 2,9],[16,-2,9]]);
SetName(f5,"f5"); SetName(f7,"f7"); SetName(f9,"f9");

# A probably very quickly contracting mapping -- proving this seems to be
# difficult anyway ...

f6q := RcwaMapping([[1,0,6],[1,1,2],[1,0,2],[1,0,3],[1,0,2],[7,1,6]]);
SetName(f6q,"f6q");

#############################################################################
##
##  Section 4.3: Checking a result by P. Andaloro
##
T := RcwaMapping([[1,0,2],[3,1,2]]); SetName(T,"T");

#############################################################################
##
##  Section 4.4: Two examples by Matthews and Leigh
##
##  The Matthews-Leigh examples -- the trajectories of 1 resp. x^3+x+1 can be
##  shown to be divergent, and their iterates can be shown to be non-cyclic
##  (mod x).
##
x := Indeterminate(GF(2),1); SetName(x,"x");
R := PolynomialRing(GF(2),1); 

ML1 := RcwaMapping(R,x,[[1,0,x],[(x+1)^3,1,x]]*One(R)); SetName(ML1,"ML1");
ML2 := RcwaMapping(R,x,[[1,0,x],[(x+1)^2,1,x]]*One(R)); SetName(ML2,"ML2");

ChangePoints := l -> Filtered([1..Length(l)-1],pos->l[pos]<>l[pos+1]);
Diffs        := l -> List([1..Length(l)-1],pos->l[pos+1]-l[pos]);

#############################################################################
##
##  Section 4.5: Exploring the structure of a wild rcwa group
##
u := RcwaMapping([[3,0,5],[9,1,5],[3,-1,5],[9,-2,5],[9,4,5]]);
SetName(u,"u");

# The following mapping is wild, but all cycles of integers |n| < 29 are
# finite. It has been constructed in a similar way as `u'.

f5_12 := RcwaMapping([[5, 0,6],[5,3,4],[5,-4,6],[5,-3,4],
                      [5, 4,6],[5,3,4],[5, 0,6],[5,-3,4],
                      [5,-4,6],[5,3,4],[5, 4,6],[5,-3,4]]);
SetName(f5_12,"f5_12");

# The following mapping has modulus 5 and multiplier 16 (this is the largest
# possible multiplier of a mapping with this modulus).

Mod5Mult16 := RcwaMapping([[16,0,5],[16,24,5],[8,4,5],[4,-2,5],[2,-3,5]]);
SetName(Mod5Mult16,"Mod5Mult16");

#############################################################################
##
##  Section 4.6: A wild rcwa mapping which has only finite cycles
##
kappa := RcwaMapping([[1,0,1],[1,0,1],[3,2,2],[1,-1,1],
                      [2,0,1],[1,0,1],[3,2,2],[1,-1,1],
                      [1,1,3],[1,0,1],[3,2,2],[2,-2,1]]);
SetName(kappa,"kappa");

kappaZ := RcwaMapping([[2, 8,1],[1,-1,1],[3,2,2],[1, 2,1],
                       [1,-3,1],[1,-3,1],[3,2,2],[1, 2,1],
                       [1, 1,3],[1,-3,1],[3,2,2],[2,-2,1]]);
SetName(kappaZ,"kappaZ");

# An example of a mapping with an infinite cycle traversing the residue
# classes (mod 12) acyclically, but having positive density as a subset of Z
# (apparently 3/8).

kappatilde := RcwaMapping([[2,-4,1],[3, 33,1],[3,2,2],[1,-1,1],
                           [2, 0,1],[3,-39,1],[3,2,2],[1,-1,1],
                           [1, 1,3],[3, 33,1],[3,2,2],[1, 4,3]]);
SetName(kappatilde,"kappatilde");

# Slight modifications which also have only finite cycles.

kappa12_fincyc := RcwaMapping([[2,-4,1],[3,-3,1],[3,2,2],[1,-1,1],
                               [2, 0,1],[3,-3,1],[3,2,2],[1,-1,1],
                               [1, 1,3],[3,-3,1],[3,2,2],[1, 4,3]]);
SetName(kappa12_fincyc,"kappa12_fincyc");

kappa24_fincyc := RcwaMapping([[1, 0,1],[1, 0,1],[1,0,1],[1, 0,1],
                               [3, 4,2],[1,-1,1],[1,0,1],[6,-2,1],
                               [2, 0,1],[1, 0,1],[1,0,1],[1, 0,1],
                               [3, 4,2],[1,-1,1],[1,0,1],[6,-2,1],
                               [1,-1,3],[1, 0,1],[1,0,1],[1, 0,1],
                               [3, 4,2],[1, 0,3],[1,0,1],[6,-2,1]]);
SetName(kappa24_fincyc,"kappa24_fincyc");

# A mapping which has finite cycles of unbounded length and, like the
# mapping `kappatilde' above, apparently one ``chaotically behaving''
# infinite cycle which has positive density (apparently 11/48) as
# a subset of Z.

kappa24_densecyc := RcwaMapping([[1, 0,1],[1, 0,1],[1,0,1],[1,  0,1],
                                 [3, 4,2],[1,-1,1],[6,4,1],[1, 23,1],
                                 [2, 0,1],[1, 0,1],[1,0,1],[1,  0,1],
                                 [3, 4,2],[1,-1,1],[6,4,1],[1,-25,1],
                                 [1,-1,3],[1, 0,1],[1,0,1],[1,  0,1],
                                 [3, 4,2],[1, 0,3],[6,4,1],[1, 23,1]]);
SetName(kappa24_densecyc,"kappa24_densecyc");

# As above, but the density now seems to be 1/6.

kappa24_onesixthcyc := RcwaMapping([[1, 0,1],[1, 0,1],[1,0,1],[1,   0,1],
                                    [3, 4,2],[1,-1,1],[1,0,1],[6, 142,1],
                                    [2, 0,1],[1, 0,1],[1,0,1],[1,   0,1],
                                    [3, 4,2],[1,-1,1],[1,0,1],[6,-146,1],
                                    [1,-1,3],[1, 0,1],[1,0,1],[1,   0,1],
                                    [3, 4,2],[1, 0,3],[1,0,1],[6, 142,1]]);
SetName(kappa24_onesixthcyc,"kappa24_onesixthcyc");

# Apart from fixed points and three 2-cycles, the following permutation
# apparently has only one cycle, traversing the set (0(4) U 1(6) U 5(12)
# U 6(12) U 22(36) U 26(36) U 27(36)) \ {-45, -17, 4, 6, 8, 13, 17, 36, 48}
# in some sense `chaotically':

kappa36 := RcwaMapping(
             [[1,  3,3],[2, 10,1],[1,  0,1],[1,  0,1],[3, -4,2],[1, 11,1],
              [3, -6,2],[1, 13,1],[3, -8,2],[1,  0,1],[1,  0,1],[1,  0,1],
              [1,  3,3],[2, 10,1],[1,  0,1],[1,  0,1],[3, -4,2],[2, 14,1],
              [3, -6,2],[2,-11,1],[3, -8,2],[1,  0,1],[1, -4,1],[1,  0,1],
              [2, 24,1],[2, 13,1],[1,  4,1],[1, -6,3],[3, -4,2],[1, -1,1],
              [3, -6,2],[1,  1,1],[3, -8,2],[1,  0,1],[1,  0,1],[1,  0,1]]);
SetName(kappa36,"kappa36");

# Even better: apart from the fixed points 4, 6 and 8 and the transpositions
# (-17,-45), (13,36) and (17,48), the following permutation seems to have
# only one single cycle(!) on the integers:

omega := RcwaMapping(
           [[1,  3,3],[1,  9,1],[1, 14,1],[1, -7,1],[3, -4,2],[1,-14,3],
            [3, -6,2],[1, 13,1],[3, -8,2],[3, 11,1],[2, -8,1],[3,  6,1],
            [1,  3,3],[2, 10,1],[1,  4,1],[1, 15,1],[3, -4,2],[2, 14,1],
            [3, -6,2],[2,-11,1],[3, -8,2],[3, 11,1],[1, -8,1],[3,  6,1],
            [2, 24,1],[1,  9,1],[1,-11,1],[1, -6,3],[3, -4,2],[1, -1,1],
            [3, -6,2],[1,  2,3],[3, -8,2],[3, 11,1],[2, -5,1],[3,  6,1]]);
SetName(omega,"omega");

# Similar, but with smaller modulus and with only one fixed point and only
# one transposition:

kappaOneCycle := RcwaMapping([[2, 8,1],[1,-1,1],[3,2,2],[1, 2,1],
                              [1, 9,1],[1,-3,1],[3,2,2],[1, 2,1],
                              [1, 1,3],[1,-3,1],[3,2,2],[2,-2,1]]);
SetName(kappaOneCycle,"kappaOneCycle");

# The mappings <sigma1> and <sigma2> generate a non-cyclic wild group all of
# whose orbits on Z seem to be finite.

sigma1 := RcwaMapping([[1,0,1],[1,1,1],[1,1,1],[1,-2,1]]);
sigma2 := RcwaMapping([[1, 0,1],[3,3,2],[1,0,1],[2,0,1],[1,0,1],[1,0,1],
                       [1,-3,3],[3,3,2],[1,0,1],[1,0,1],[1,0,1],[1,0,1],
                       [2, 0,1],[3,3,2],[1,0,1],[1,0,1],[1,0,1],[1,0,1]]);
SetName(sigma1,"sigma1"); SetName(sigma2,"sigma2");

theta := RcwaMapping([[3, 32,16],[3,-1,2],[9,-6,4],[9,-15,2],
                      [3, 20, 8],[3,-1,2],[9,-6,4],[9,-15,2],
                      [9,-72,16],[3,-1,2],[9,-6,4],[9,-15,2],
                      [9, 12, 8],[3,-1,2],[9,-6,4],[9,-15,2]]);
SetName(theta,"theta");

sigma := sigma1 * sigma2; SetName(sigma,"sigma");

# A `simplification' of <sigma>.

sigma_r := RcwaMapping([[1, 0,1], [1, 0,1], [2, 2,1], [3,-3,2],
                        [1, 0,1], [1, 1,3], [3, 6,2], [1, 0,1],
                        [1, 0,1], [1, 0,1], [1, 0,1], [1, 0,1],
                        [2, 0,1], [1, 0,1], [1, 1,1], [3,-3,2],
                        [1, 0,1], [1, 1,1], [3, 6,2], [1, 0,1],
                        [1, 0,1], [2, 0,1], [1, 0,1], [1, 0,1],
                        [1,-9,3], [1, 0,1], [1, 1,1], [3,-3,2],
                        [1, 0,1], [2, 2,1], [3, 6,2], [1, 0,1],
                        [1, 0,1], [1, 0,1], [1, 0,1], [1, 0,1]]);
SetName(sigma_r,"sigma_r");

# The mapping <comm> is another `only finite cycles' example.

sigmas2 := RcwaMapping([[1,0,1],[1, 0,1],[3,0,2],[2,1,1],[1,0,1],[1,0,1],
                        [3,0,2],[1,-1,3],[1,0,1],[2,1,1],[3,0,2],[1,0,1]]);
SetName(sigmas2,"sigmas2");
sigmas := sigma1 * sigmas2; SetName(sigmas,"sigmas");
comm := Comm(sigmas,sigma1); SetName(comm,"comm");

#############################################################################
##
##  Section 4.7: An abelian rcwa group over a polynomial ring
##
##  As the mappings <g> and <h> are modified within the example, we denote
##  the unmodified versions by <gu> and <hu> and the modified ones by
##  <gm> and <hm>, respectively. The temporary variables have been renamed
##  to avoid name clashes.
##
x := Indeterminate(GF(4),1); SetName(x,"x");
R := PolynomialRing(GF(4),1); e := One(GF(4));
pp := x^2 + x + e;;    qq := x^2 + e;;
rr := x^2 + x + Z(4);; ss := x^2 + x + Z(4)^2;;
cg := List( AllResidues(R,x^2), pol -> [ pp, pp * pol mod qq, qq ] );;
ch := List( AllResidues(R,x^2), pol -> [ rr, rr * pol mod ss, ss ] );;
gu := RcwaMapping( R, qq, cg );
hu := RcwaMapping( R, ss, ch );
cg[1][2] := cg[1][2] + (x^2 + e) * pp * qq;;
ch[7][2] := ch[7][2] + x * rr * ss;;
gm := RcwaMapping( R, qq, cg );
hm := RcwaMapping( R, ss, ch );

# An rcwa mapping of GF(2)[x] of infinite order which has only finite cycles.
# This is the example of an rcwa mapping of a polynomial ring we gave in the
# introduction in the manual.

R := PolynomialRing(GF(2),1);
x := IndeterminatesOfPolynomialRing(R)[1]; SetName(x,"x");
e := One(GF(2)); zero := Zero(R);

r_2mod := RcwaMapping( 2, x^2 + e,
                       [ [ x^2 + x + e, zero   , x^2 + e ],
                         [ x^2 + x + e, x      , x^2 + e ],
                         [ x^2 + x + e, x^2    , x^2 + e ],
                         [ x^2 + x + e, x^2 + x, x^2 + e ] ] );
SetName(r_2mod,"r");

#############################################################################
##
##  Section 4.8: A tame group generated by commutators of wild permutations
##
a := RcwaMapping([[3,0,2],[3, 1,4],[3,0,2],[3,-1,4]]); SetName(a,"a");
b := RcwaMapping([[3,0,2],[3,13,4],[3,0,2],[3,-1,4]]); SetName(b,"b");
c := RcwaMapping([[3,0,2],[3, 1,4],[3,0,2],[3,11,4]]); SetName(c,"c");

ab := Comm(a,b); SetName(ab,"[a,b]");
ac := Comm(a,c); SetName(ac,"[a,c]");
bc := Comm(b,c); SetName(bc,"[b,c]");

# Two rcwa mappings of orders 7 and 12, respectively, which have isomorphic
# transition graphs for modulus 6 and generate the infinite tame group taken
# as an example for the use of `RespectedPartition'.

g := RcwaMapping([[2,2,1],[1, 4,1],[1,0,2],[2,2,1],[1,-4,1],[1,-2,1]]);
h := RcwaMapping([[2,2,1],[1,-2,1],[1,0,2],[2,2,1],[1,-1,1],[1, 1,1]]);
SetName(g,"g"); SetName(h,"h");

# A factorization of `a' (see above) into two balanced mappings,
# where one of them is an involution.

a_2 := RcwaMapping([List([[1,2],[36,72]],ResidueClass)]); a_1 := a/a_2;
SetName(a_1,"a_1"); SetName(a_2,"a_2");

#############################################################################
##
##  Section 4.9: Checking for solvability
##
a := RcwaMapping([[3,0,2],[3, 1,4],[3,0,2],[3,-1,4]]); SetName(a,"a");
b := RcwaMapping([[3,0,2],[3,13,4],[3,0,2],[3,-1,4]]); SetName(b,"b");

#############################################################################
##
##  Section 4.10: Some examples over (semi)localizations of the integers
##
a2  := RcwaMapping(Z_pi(2),    ShallowCopy(Coefficients(a)));

a23 := RcwaMapping(Z_pi([2,3]),ShallowCopy(Coefficients(a)));
b23 := RcwaMapping(Z_pi([2,3]),ShallowCopy(Coefficients(b)));
c23 := RcwaMapping(Z_pi([2,3]),ShallowCopy(Coefficients(c)));

ab23 := Comm(a23,b23); ac23 := Comm(a23,c23);

SetName(a2,"a2");
SetName(a23,"a23"); SetName(b23,"b23"); SetName(c23,"c23");
SetName(ab23,"[a23,b23]"); SetName(ac23,"[a23,c23]");

v := RcwaMapping([[6,0,1],[1,-7,2],[6,0,1],[1,-1,1],
                  [6,0,1],[1, 1,2],[6,0,1],[1,-1,1]]);

v2 := RcwaMapping(Z_pi(2),ShallowCopy(Coefficients(v)));
w2 := RcwaMapping(Z_pi(2),[[1,0,2],[2,-1,1],[1,1,1],[2,-1,1]]);
SetName(v,"v"); SetName(v2,"v2"); SetName(w2,"w2");

v2w2 := Comm(v2,w2); SetName(v2w2,"[v2,w2]");

#############################################################################
##
##  Section 4.11: Twisting 257-cycles into an rcwa mapping with modulus 32
##
##  In order to avoid a name clash we call the mapping `x_257' instead
##  of `x'.
##
x_257 := RcwaMapping([[ 16,  2,  1], [ 16, 18,  1],
                      [  1, 16,  1], [ 16, 18,  1],
                      [  1, 16,  1], [ 16, 18,  1],
                      [  1, 16,  1], [ 16, 18,  1],
                      [  1, 16,  1], [ 16, 18,  1],
                      [  1, 16,  1], [ 16, 18,  1],
                      [  1, 16,  1], [ 16, 18,  1],
                      [  1, 16,  1], [ 16, 18,  1],
                      [  1,  0, 16], [ 16, 18,  1],
                      [  1,-14,  1], [ 16, 18,  1],
                      [  1,-14,  1], [ 16, 18,  1],
                      [  1,-14,  1], [ 16, 18,  1],
                      [  1,-14,  1], [ 16, 18,  1],
                      [  1,-14,  1], [ 16, 18,  1],
                      [  1,-14,  1], [ 16, 18,  1],
                      [  1,-14,  1], [  1,-31,  1]]);
SetName(x_257,"x");

#############################################################################
##
##  Section 4.12: The behaviour of the moduli of powers
##
##  We only list mappings here which are used exclusively in this example.
##
v6 := RcwaMapping([[-1,2,1],[1,-1,1],[1,-1,1]]);
w8 := RcwaMapping([[-1,3,1],[1,-1,1],[1,-1,1],[1,-1,1]]);
SetName(v6,"v6"); SetName(w8,"w8");

z := RcwaMapping([[2,  1, 1],[1,  1,1],[2, -1,1],[2, -2,1],
                  [1,  6, 2],[1,  1,1],[1, -6,2],[2,  5,1],
                  [1,  6, 2],[1,  1,1],[1,  1,1],[2, -5,1],
                  [1,  0, 1],[1, -4,1],[1,  0,1],[2,-10,1]]);
SetName(z,"z");

e1 := RcwaMapping([[1,4,1],[2,0,1],[1,0,2],[2,0,1]]); SetName(e1,"e1");
e2 := RcwaMapping([[1,4,1],[2,0,1],[1,0,2],[1,0,1],
                   [1,4,1],[2,0,1],[1,0,1],[1,0,1]]); SetName(e2,"e2");

#############################################################################
##
##  Section 4.13: Images and preimages under the Collatz mapping
##
T := RcwaMapping([[1,0,2],[3,1,2]]); SetName(T,"T");

T5 := RcwaMapping([[1,0,2],[5,-1,2]]); SetName(T5,"T5");

#############################################################################
##
##  Replacing the Collatz mapping by conjugates
##
##  This example has been removed from the manual (too trivial).
##
T := RcwaMapping([[1,0,2],[3,1,2]]); SetName(T,"T");
a := RcwaMapping([[3,0,2],[3, 1,4],[3,0,2],[3,-1,4]]); SetName(a,"a");

#############################################################################
##
##  Section 4.14: A group which acts 4-transitively on the positive integers
##
a := RcwaMapping([[3,0,2],[3, 1,4],[3,0,2],[3,-1,4]]); SetName(a,"a");
u := RcwaMapping([[3,0,5],[9,1,5],[3,-1,5],[9,-2,5],[9,4,5]]);
SetName(u,"u");

#############################################################################
##
##  Section 4.15: A group which acts 3-, but not 4-transitively on Z
##
##  This example does not define rcwa mappings whose inclusion here would
##  save any typing.
##

#############################################################################
##
##  Section 4.16: Grigorchuk groups
##
##  The definition of a, b, c and d is omitted in order to avoid overwriting
##  the previous values of these variables.
##
SequenceElement := function ( r, level )

  return Permutation(Product(Filtered([1..level-1],k->k mod 3 <> r),
                             k->ClassTransposition(    2^(k-1)-1, 2^(k+1),
                                                   2^k+2^(k-1)-1, 2^(k+1))),
                     [0..2^level-1]);
end;

FourCycle := RcwaMapping((4,5,6,7),[4..7]);

GrigorchukGroup2Generator := function ( level )
  if level = 1 then return FourCycle; else
    return   Restriction(FourCycle, RcwaMapping([[4,1,1]]))
           * Restriction(FourCycle, RcwaMapping([[4,3,1]]))
           * Restriction(GrigorchukGroup2Generator(level-1),
                         RcwaMapping([[4,0,1]]));
  fi;
end;

GrigorchukGroup2 := level -> Group(FourCycle,
                                   GrigorchukGroup2Generator(level));

#############################################################################
##
##  Section 4.17: Forward orbits of a monoid with 2 generators
##
T5m := RcwaMapping([[1,0,2],[5,-1,2]]);; SetName(T5m,"T5-");
T5p := RcwaMapping([[1,0,2],[5, 1,2]]);; SetName(T5p,"T5+");

#############################################################################
##
##  Section 4.18: Representations of the free group of rank 2
##
r1 := ClassTransposition(0,2,1,2) * ClassTransposition(0,2,1,4);
r2 := ClassTransposition(0,2,1,2) * ClassTransposition(0,2,3,4);
SetName(r1,"r1"); SetName(r2,"r2");

F2 := Group(r1^2,r2^2); SetName(F2,"F_2");

#############################################################################
##
##  Section 4.19: Representations of the modular group PSL(2,Z)
##
PSL2Z := Group(ClassTransposition(0,3,1,3) * ClassTransposition(0,3,2,3),
               ClassTransposition(1,3,0,6) * ClassTransposition(2,3,3,6));
SetName(PSL2Z,"PSL(2,Z)");

#############################################################################
##
##  It seems that the group G defined below has the following infinite
##  presentation:
##
##  G = < a,b | [a^(2k+1),b^l]^(4^l) = 1, k,l in N >
##
GInvPres := Group(ClassShift(0,2),
                  ClassTransposition(0,2,1,2) * ClassTransposition(3,4,5,8)
                * ClassTransposition(0,2,1,8));

#############################################################################
##
##  A permutation with cycle lengths 12 + 6k, k in N_0
##
##  The name reflects the shape of the transition graph.
##
Hexagon := RcwaMapping(
             [ [ 1,  0, 1 ], [ 1,  0, 1 ], [ 3,  -2, 2 ], [ 2,  3, 3 ],
               [ 1,  0, 1 ], [ 2,  5, 3 ], [ 3,  -6, 2 ], [ 2,  7, 3 ],
               [ 1,  0, 1 ], [ 1,  0, 1 ], [ 3, -10, 2 ], [ 1,  0, 1 ],
               [ 1,  0, 1 ], [ 1,  0, 1 ], [ 3,  -2, 2 ], [ 1,  7, 1 ],
               [ 1,  0, 1 ], [ 1, -3, 1 ], [ 3,  -6, 2 ], [ 1, -1, 1 ],
               [ 1,  1, 1 ], [ 2,  3, 3 ], [ 3, -10, 2 ], [ 2,  5, 3 ],
               [ 1, -1, 1 ], [ 2,  7, 3 ], [ 3,  -2, 2 ], [ 1,  7, 1 ],
               [ 1, -3, 1 ], [ 1, -3, 1 ], [ 3,  -6, 2 ], [ 1, -1, 1 ],
               [ 1,  0, 1 ], [ 1,  0, 1 ], [ 3, -10, 2 ], [ 1,  0, 1 ] ] );
SetName(Hexagon,"Hexagon");
HexagonFacts := Factorization(Hexagon);
Hexagon1     := Product(HexagonFacts{[1..13]});  # integral perm. of order 4
Hexagon2     := Product(HexagonFacts{[14..22]}); # an involution

#############################################################################
##
##  A permutation with finite cycles of various lengths,
##  and likely also infinite cycles
##
##  The name again reflects the shape of the transition graph. Cycle lengths
##  are e.g. 12, 14, 15, 18, 21, 30, 36, 42, 48. Constructing the permutation
##  needs a couple of seconds, thus the code is wrapped into a function to
##  avoid it being executed at any time this file is read into GAP.
##
Hexagon235 := function ( )

  local  edges, classes, source, range, fixed;

  edges :=
    [[1,60,1,90],[2,90,2,60],[3,20,3,50],[4,50,4,20],[5,45,5,75],[6,75,6,45],
     [91,720,23,100],[271,720,43,100],[451,720,63,100],[631,720,83,100],
     [53,200,81,225],[153,200,156,225],
     [51,225,92,720],[96,225,272,720],[141,225,452,720],[186,225,632,720],
     [62,180,54,200],[122,180,154,200],
     [24,100,50,225],[44,100,95,225],[64,100,140,225],[84,100,185,225],
     [80,225,61,180],[155,225,121,180]];

  classes := List(edges,edge->[ResidueClass(edge[1],edge[2]),
                               ResidueClass(edge[3],edge[4])]);

  source := List(classes,cls->cls[1]);
  range  := List(classes,cls->cls[2]);

  fixed  := Difference(Integers,Union(source));

  Append(source,AsUnionOfFewClasses(fixed));
  Append(range, AsUnionOfFewClasses(fixed));

  return RepresentativeAction(RCWA(Integers),source,range);

end;

#############################################################################
##
##  A group which has any symmetric group of odd degree as a quotient
##
SmOdd := Group( ClassTransposition(0,4,3,4),
                ClassTransposition(0,6,3,6),
                ClassTransposition(1,4,0,6) );

#############################################################################
##
##  The ``Class Transposition Graph''
##
##  The vertices of the `Class Transposition Graph' are the class transposi-
##  tions. Two vertices are connected by an edge if their product is tame.
##
##  Below, examples of embeddings of all 11 graphs with 4 vertices into this
##  graph are listed. The function `CheckGraphEmbeddings' can be used to
##  check this data. If it detects an error, it raises an error message and
##  enters a break loop.
##
Embeddings4 := [
  [ [  ],
    [ ClassTransposition(0,2,1,2), ClassTransposition(0,2,1,4),
      ClassTransposition(0,2,1,6), ClassTransposition(0,2,1,8) ] ],
  [ [ [ 1, 2 ] ],
    [ ClassTransposition(0,4,1,4), ClassTransposition(2,4,3,4),
      ClassTransposition(0,2,1,6), ClassTransposition(0,2,1,10) ] ],
  [ [ [ 1, 2 ], [ 1, 3 ] ],
    [ ClassTransposition(1,4,4,6), ClassTransposition(1,2,0,6),
      ClassTransposition(3,4,0,6), ClassTransposition(0,2,1,2) ] ],
  [ [ [ 1, 2 ], [ 3, 4 ] ],
    [ ClassTransposition(1,2,0,6), ClassTransposition(3,4,2,6),
      ClassTransposition(0,2,3,6), ClassTransposition(2,4,5,6) ] ],
  [ [ [ 1, 2 ], [ 1, 3 ], [ 1, 4 ] ],
    [ ClassTransposition(1,3,0,6), ClassTransposition(1,3,2,3),
      ClassTransposition(3,4,2,6), ClassTransposition(2,4,1,6) ] ],
  [ [ [ 1, 2 ], [ 1, 3 ], [ 2, 3 ] ],
    [ ClassTransposition(1,3,2,3), ClassTransposition(1,6,2,6),
      ClassTransposition(0,4,3,6), ClassTransposition(0,2,3,4) ] ],
  [ [ [ 1, 2 ], [ 1, 3 ], [ 2, 4 ] ],
    [ ClassTransposition(1,6,4,6), ClassTransposition(0,4,3,6),
      ClassTransposition(1,2,2,6), ClassTransposition(2,4,1,6) ] ],
  [ [ [ 1, 2 ], [ 1, 3 ], [ 1, 4 ], [ 2, 3 ] ],
    [ ClassTransposition(3,6,4,6), ClassTransposition(0,3,2,6),
      ClassTransposition(1,3,2,6), ClassTransposition(1,5,2,5) ] ],
  [ [ [ 1, 2 ], [ 1, 3 ], [ 2, 4 ], [ 3, 4 ] ],
    [ ClassTransposition(2,4,3,4), ClassTransposition(0,4,2,4),
      ClassTransposition(1,3,0,6), ClassTransposition(1,3,5,6) ] ],
  [ [ [ 1, 2 ], [ 1, 3 ], [ 1, 4 ], [ 2, 3 ], [ 2, 4 ] ],
    [ ClassTransposition(3,6,4,6), ClassTransposition(1,5,3,5),
      ClassTransposition(0,2,1,2), ClassTransposition(1,2,2,6) ] ],
  [ [ [ 1, 2 ], [ 1, 3 ], [ 1, 4 ], [ 2, 3 ], [ 2, 4 ], [ 3, 4 ] ],
    [ ClassTransposition(0,3,2,3), ClassTransposition(0,4,3,4),
      ClassTransposition(3,6,4,6), ClassTransposition(2,6,5,6) ] ] ];

CheckGraphEmbeddings := function ( embeddingslist )
  
  local  i, pairs, deg;

  deg   := Maximum(Filtered(Flat(embeddingslist),IsInt));
  pairs := Combinations([1..deg],2);
  for i in [1..Length(embeddingslist)] do
    if   Filtered(pairs,pair->IsTame(Product(embeddingslist[i][2]{pair})))
      <> embeddingslist[i][1]
    then Error("graph embeddings list is wrong!!!\n"); fi;
  od;
  return true;
end;

#############################################################################
##
##  The Venturini examples.
##
##  The examples V0 - V8 below are taken from
##
##  G. Venturini. Iterates of number-theoretic functions with periodic
##  rational coefficients (generalization of the 3x+1 problem).
##  Stud. Appl. Math., 86(3):185--218, 1992.
##
V0 := RcwaMapping([[2,0,3],[4,5,3],[4,-5,3]]); # The residue class 0(5)
                                               # is an ergodic set of V0.

V1 := function ( t )

        local map;

        map := RcwaMapping([[2500,6     ,6],[t,  -t+4,2],[1,16,6],
                            [t   ,-3*t+4,2],[t,-4*t+4,2],[1,13,6]]);
        SetName(map,Concatenation("V1(",String(t),")"));
        return map;
      end;

V2 := function ( k, p, t )

        local  map, c, r;

        if not IsSubset(PositiveIntegers,[k,p,t])
          or t < 1 or t >= p or Gcd(p,t) <> 1 then return fail;
        fi;
        c := [[p^(k-1),1,1]];
        for r in [1..p-1] do c[r+1] := [t,r*(p-t),p]; od;
        map := RcwaMapping(c);
        SetName(map,Concatenation("V2(",String(k),",",String(p),",",
                                        String(t),")"));
        return map;
      end;

V3 := function ( t )

        local map;

        map := RcwaMapping([[ 1, 0,4],[1,  1,2],[20,    -40,1],[1,-3,8],
                            [20,48,1],[3,-13,2],[ t,-6*t+64,4],[1, 1,8]]);
        SetName(map,Concatenation("V3(",String(t),")"));
        return map;
      end;

V4 := RcwaMapping([[9, 1,1],[  1,  32,3],[1,-2,3],
                   [1, 3,1],[100,-364,9],[1,-5,3],
                   [1,-6,1],[100,-637,9],[1,-8,3]]);

V5 := RcwaMapping([[1,0,6],[2,16,3],[3,11,1],[1,-3,6],[1,-4,1],[1,9,2]]);

V6 := RcwaMapping([[1,  4,2],[1,  3,2],[ 1,  2, 2],[ 1,  1, 2],[ 1,  0, 2],
                   [5,-17,2],[5,-22,2],[17,-39,10],[17,-56,10],[17,-73,10]]);

V7 := RcwaMapping([[1,0,3],[2,-2,3],[5,-4,3],[4,0,3],[5,-8,3],[4,-2,3]]);

V8 := RcwaMapping([[1,0,3],[1,-1,3],[5,5,3],[3,5,2],[3,2,2],[3,-1,2]]);

SetName(V0,"V0"); SetName(V4,"V4"); SetName(V5,"V5");
SetName(V6,"V6"); SetName(V7,"V7"); SetName(V8,"V8");

#############################################################################
##
##  An example by H. M. Farkas.
##
##  The following mapping has no divergent trajectories, but trajectories
##  which ascend any given number of consecutive steps. Proof: elementary.
##
Farkas := RcwaMapping([[1,0,3],[1,1,2],[1,0,1],[1,0,3],
                       [1,0,1],[1,1,2],[1,0,3],[3,1,2],
                       [1,0,1],[1,0,3],[1,0,1],[3,1,2]]);
SetName(Farkas,"Farkas");

#############################################################################
##
##  The mappings defined in the preprint ``Symmetrizing the 3n+1 Tree''.
##
l := RcwaMapping([[1,0,1],[1,0,1],[ 4,0,1],
                  [1,0,1],[1,0,1],[ 1,0,1],
                  [1,0,1],[1,0,1],[16,0,1]]);
SetName(l,"l");

r := RcwaMapping([[1,0,1],[1,0,1],[ 4,-2,3],
                  [1,0,1],[1,0,1],[ 1, 0,1],
                  [1,0,1],[1,0,1],[ 8,-4,3],
                  [1,0,1],[1,0,1],[16,-8,3],
                  [1,0,1],[1,0,1],[ 1, 0,1],
                  [1,0,1],[1,0,1],[ 2,-1,3],
                  [1,0,1],[1,0,1],[ 4,-2,3],
                  [1,0,1],[1,0,1],[ 1, 0,1],
                  [1,0,1],[1,0,1],[ 2,-1,3]]);
SetName(r,"r");

d := RcwaMapping([[1,0,1],[1,0,1],[3,2,4],[1,0,1],
                  [1,0,1],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,4],[1,0,1],[1,0,1],[3,1,2],
                  [1,0,1],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,1],[3,1,2],[1,0,1],[1,0,1],
                  [3,4,8],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,1],[1,0,1],[3,2,4],[1,0,1],
                  [1,0,1],[3,1,2],[1,0,1],[1,0,1],
                  [1,0,1],[1,0,1],[1,0,1],[3,1,2],
                  [1,0,1],[1,0,1],[3,2,4],[1,0,1],
                  [1,0,1],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,4],[1,0,1],[1,0,1],[3,1,2],
                  [1,0,1],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,1],[3,1,2],[1,0,1],[1,0,1],
                  [3,8,16],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,1],[1,0,1],[3,2,4],[1,0,1],
                  [1,0,1],[3,1,2],[1,0,1],[1,0,1],
                  [1,0,1],[1,0,1],[1,0,1],[3,1,2],
                  [1,0,1],[1,0,1],[3,2,4],[1,0,1],
                  [1,0,1],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,4],[1,0,1],[1,0,1],[3,1,2],
                  [1,0,1],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,1],[3,1,2],[1,0,1],[1,0,1],
                  [3,4,8],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,1],[1,0,1],[3,2,4],[1,0,1],
                  [1,0,1],[3,1,2],[1,0,1],[1,0,1],
                  [1,0,1],[1,0,1],[1,0,1],[3,1,2],
                  [1,0,1],[1,0,1],[3,2,4],[1,0,1],
                  [1,0,1],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,4],[1,0,1],[1,0,1],[3,1,2],
                  [1,0,1],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,1],[3,1,2],[1,0,1],[1,0,1],
                  [1,0,16],[1,0,1],[1,0,1],[1,0,1],
                  [1,0,1],[1,0,1],[3,2,4],[1,0,1],
                  [1,0,1],[3,1,2],[1,0,1],[1,0,1],
                  [1,0,1],[1,0,1],[1,0,1],[3,1,2]]);
SetName(d,"d");

f := RcwaMapping([[2,0,1]])
   * RepresentativeAction(RCWA(Integers),ResidueClass(0,2),MovedPoints(l));
SetName(f,"f");

finv := RcwaMapping([[1,0,1],[1,0,1],[2,-4,9],
                     [1,0,1],[1,0,1],[1, 0,1],
                     [1,0,1],[1,0,1],[2,-7,9]]);
SetName(finv,"finv");

L := f*l*finv; SetName(L,"L");
R := f*r*finv; SetName(R,"R");
D := f*d*finv; SetName(D,"D");

# The function `LRWord' is a bijection from the positive integers to the
# free monoid F if and only if the 3n+1 Conjecture holds.

F := FreeMonoid("L","R");

LRWord := function ( n )

  local  l, imL, imR, w, i;

  if not IsPosInt(n) then return fail; fi;
  if n = 1 then return One(F); fi;
  imL := Image(L); imR := Image(R);
  l := Trajectory(D,n,1,"stop");
  w := [];
  for i in [Length(l)-1,Length(l)-2..1] do
    if l[i] in imL then Add(w,F.1); else Add(w,F.2); fi;
  od;
  return Product(w);
end;

# The mapping `TreeSortingPerm' is a permutation of the positive integers if
# and only if the 3n+1 Conjecture holds.

TreeSortingPerm := MappingByFunction( PositiveIntegers, PositiveIntegers,

function ( n ) # The conjectured permutation ...

  local  l, imL, imR, m, i;

  if not IsPosInt(n) then return fail; fi;
  if n = 1 then return 1; fi;
  imL := Image(L); imR := Image(R);
  l := Trajectory(D,n,1,"stop");
  m := 1;
  for i in [Length(l)-1,Length(l)-2..1] do
    if l[i] in imL then m := 2*m; else m := 2*m+1; fi;
  od;
  return m;
end,

function ( n ) # ... and its inverse.

  local  l, m, i;

  if not IsPosInt(n) then return fail; fi;
  if n = 1 then return 1; fi;
  l := Reversed(CoefficientsQadic(n,2));
  m := 1;
  for i in [2..Length(l)] do
    if l[i] = 0 then m := m^L; else m := m^R; fi;
  od;
  return m;
end );

# Other pairs of mappings like (L,R).

L2 := RcwaMapping([[3,0,1]]); SetName(L2,"L2");
R2 := RcwaMapping([[3,1,1],[3,5,2],[3,1,1],[3,-1,4]]); SetName(R2,"R2");
D2 := CommonRightInverse(L2,R2); SetName(D2,"D2");

L3 := RcwaMapping([[3,0,1]]); SetName(L3,"L3");
R3 := RcwaMapping(List([[0, 2],[ 3, 4],[ 1,20],[5,20],
                        [9,20],[13,20],[17,20]],ResidueClass),
                  List([[ 1, 6],[ 2, 3],[ 4,12],[10,48],
                        [22,48],[34,48],[46,48]],ResidueClass));
SetName(R3,"R3");
D3 := CommonRightInverse(L3,R3); SetName(D3,"D3");

L4 := 8 * IdentityRcwaMappingOfZ;
R4 := RcwaMapping([[8,5,5],[8,12,5],[8,9,5],[4,-2,5],[4,-1,5]]);
D4 := CommonRightInverse(L4,R4);
SetName(L4,"L4");  SetName(R4,"R4"); SetName(D4,"D4");

# A pair (L,R) which spans a tree which definitely has not all positive
# integers as vertices.

L5 := RcwaMapping(List([[0, 2],[1,4],[3, 8],[7,8]],ResidueClass),
                  List([[0,16],[4,8],[8,16],[2,4]],ResidueClass));
SetName(L5,"L5");
R5 := RcwaMapping(List([[0,2],[1, 4],[ 3, 8],[7,8]],ResidueClass),
                  List([[1,8],[5,16],[13,16],[3,4]],ResidueClass));
SetName(R5,"R5");
D5 := CommonRightInverse(L5,R5); SetName(D5,"D5");

#############################################################################
##
##  An rcwa representation of Syl_3(S_9)
##
##  This example has been removed from the manual, since it was thought to be
##  too trivial compared to the others.
##
r := RcwaMapping([[1,0,1],[1,1,1],[3, -3,1],
                  [1,0,3],[1,1,1],[3, -3,1],
                  [1,0,1],[1,1,1],[3, -3,1]]); SetName(r,"r");
s := RcwaMapping([[1,0,1],[1,1,1],[3,  6,1],
                  [1,0,3],[1,1,1],[3,  6,1],
                  [1,0,1],[1,1,1],[3,-21,1]]); SetName(s,"s");

#############################################################################
##
##  Involutions whose product has coprime multiplier and divisor
##
##  This example has been removed from the manual, since involutions having
##  this property can now easily be obtained as factors of ``PrimeSwitches''.
##  The construction of the latter has been found by generalizing this
##  example to primes other than 3.
##
f1 := RcwaMapping([List([[1,6],[0, 8]],ResidueClass),
                   List([[5,6],[4, 8]],ResidueClass)]); SetName(f1,"f1");
f2 := RcwaMapping([List([[1,6],[0, 4]],ResidueClass),
                   List([[2,4],[5, 6]],ResidueClass)]); SetName(f2,"f2");
f3 := RcwaMapping([List([[2,6],[1,12]],ResidueClass),
                   List([[4,6],[7,12]],ResidueClass)]); SetName(f3,"f3");

f12 := f1*f2; SetName(f12,"f12");
f23 := f2*f3; SetName(f23,"f23"); # Only finite cycles (?)
f13 := f1*f3; SetName(f13,"f13"); #  "     "      "    (?)

f := f1*f2*f3; SetName(f,"f");

# Two tame mappings (of orders 3 and 2, respectively), whose product is not
# balanced.

g1 := RcwaMapping([[6,2,1],[1,-1,1],[1,4,6],[6,2,1],[1,-1,1],[1,0,1],
                   [6,2,1],[1,-1,1],[1,0,1],[6,2,1],[1,-1,1],[1,0,1],
                   [6,2,1],[1,-1,1],[1,0,1],[6,2,1],[1,-1,1],[1,0,1]]);

g2 := RcwaMapping([[1,0,1],[3,-1,1],[1,1,3],[1,0,1],[1,0,1],[1,0,1],
                   [1,0,1],[3,-1,1],[1,0,1],[1,0,1],[1,0,1],[1,0,1],
                   [1,0,1],[3,-1,1],[1,0,1],[1,0,1],[1,0,1],[1,0,1]]);

SetName(g1,"g1"); SetName(g2,"g2");

# Two mappings whose commutator is not balanced.

c1 := Restriction(RcwaMapping([[2,0,3],[4,-1,3],[4,1,3]]),
                  RcwaMapping([[2,0,1]]));
c2 := RcwaMapping([[1,0,2],[2,1,1],[1,-1,1],[2,1,1]]);
SetName(c1,"c1"); SetName(c2,"c2");

#############################################################################
##
##  A factorization of Collatz' permutation into involutions. 
##
##  The following factorization has been determined interactively, before
##  the general factorization routine `FactorizationIntoCSCRCT' has been
##  implemented. The determination of this factorization gave the necessary
##  insights to develop a general method.
##
INTEGRAL_PART_COEFFS :=
[ -3, -26, -47, -40, 47, -1, 0, 17, 0, -4, 0, 28, 19, 12, 0, 2, -7, 20, 0,
  -3, 0, 12, 0, 37, -3, 4, 0, 13, -9, -1, 0, 17, 0, 2, 0, 70, 38, 12, 0, 2,
  3, -26, 0, -30, 0, 30, 0, 144, 19, -26, 0, -40, -7, -1, 0, 17, 0, -4, 0,
  28, -3, 12, 0, 2, -9, 20, 0, -3, 0, -57, 0, -35, -3, 4, -47, 13, 47, -1, 0,
  17, 0, 2, 0, -76, 19, 12, 0, 2, -7, -26, 0, -30, 0, 54, 0, 37, -3, -26, 0,
  -40, -9, -1, 0, 17, 0, -4, 0, 28, 38, 12, 0, 2, 3, 20, 0, -3, 0, -22, 0,
  24, 19, 4, 0, 13, -7, -1, 0, 17, 0, 2, 0, -52, -3, 12, 0, 2, -9, -26, 0,
  -30, 0, -57, 0, -35, -3, -26, -47, -40, 47, -1, 0, 17, 0, -4, 0, 28, 19,
  12, 0, 2, -7, 20, 0, -3, 0, 12, 0, 37, -3, 4, 0, 13, -9, -1, 0, 17, 0, 2,
  0, 70, 38, 12, 0, 2, 3, -26, 0, -30, 0, 30, 0, 96, 19, -26, 0, -40, -7, -1,
  0, 17, 0, -4, 0, 28, -3, 12, 0, 2, -9, 20, 0, -3, 0, -57, 0, -35, -3, 4,
  -47, 13, 47, -1, 0, 17, 0, 2, 0, -76, 19, 12, 0, 2, -7, -26, 0, -30, 0, 54,
  0, 37, -3, -26, 0, -40, -9, -1, 0, 17, 0, -4, 0, 28, 38, 12, 0, 2, 3, 20,
  0, -3, 0, -214, 0, -24, 19, 4, 0, 13, -7, -1, 0, 17, 0, 2, 0, -52, -3, 12,
  0, 2, -9, -26, 0, -30, 0, -57, 0, -35 ];

rc := function(r,m) return ResidueClass(DefaultRing(m),m,r); end;

FactorsOfCollatzPermutation := [
  RcwaMapping(List(INTEGRAL_PART_COEFFS,b_rm->[1,b_rm,1])), nu^-4,
  RcwaMapping([[rc(3,144),rc(139,288)],[rc(75,144),rc(235,288)]]),
  RcwaMapping([[rc(101,144),rc(43,288)]]),
  RcwaMapping([[rc(27,36),rc(23,72)],[rc(17,36),rc(47,72)],
               [rc(70,72),rc(71,144)],[rc(65,72),rc(143,144)]]),
  RcwaMapping([[rc(29,144),rc(91,288)]]),
  RcwaMapping([[rc(27,36),rc(70,72)],[rc(17,36),rc(3,72)]]),
  RcwaMapping([[rc(29,72),rc(187,288)],[rc(65,72),rc(283,288)]]),
  RcwaMapping([[rc(3,36),rc(8,72)],[rc(5,36),rc(32,72)],
               [rc(15,36),rc(56,72)]]),
  RcwaMapping([[rc(3,36),rc(91,288)],[rc(5,36),rc(187,288)],
               [rc(15,36),rc(283,288)]]),
  RcwaMapping([[rc(23,24),rc(7,48)],[rc(8,24),rc(33,48)],
               [rc(13,24),rc(43,96)]]),
  RcwaMapping([[rc(17,36),rc(91,288)],[rc(29,36),rc(283,288)]]),
  RcwaMapping([[rc(20,24),rc(4,12)],[rc(19,48),rc(21,24)]]),
  RcwaMapping([[rc(283,288),rc(29,36)]]),
  RcwaMapping([[rc(3,36),rc(1,48)],[rc(15,36),rc(25,48)],
               [rc(27,36),rc(11,48)],[rc(5,36),rc(35,48)],
               [rc(17,36),rc(36,48)],[rc(29,36),rc(9,48)],
               [rc(91,288),rc(33,48)],[rc(187,288),rc(20,24)],
               [rc(283,288),rc(7,48)]]), f, nu^4, f^4 ];

FACTORS_OF_CP_CYCS := List([1,2,4,12,112,156,256],
                           n->Cycle(FactorsOfCollatzPermutation[1],n)
                              mod 288);

nu_rm := ClassShift; t_rm := ClassReflection;

InvolutionFactorsOfCollatzPermutation := Concatenation(
  [ t_rm(  0,288), t_rm(  0,288) * nu_rm(  0,288)^-1,
    t_rm(  1,288), t_rm(  1,288) * nu_rm(  1,288)^-1,
    t_rm(  2,288), t_rm(  2,288) * nu_rm(  2,288)^-1,
    t_rm(  3,288), t_rm(  3,288) * nu_rm(  3,288)^-1,
    t_rm(237,288), t_rm(237,288) * nu_rm(237,288),
    t_rm(252,288), t_rm(252,288) * nu_rm(252,288),
    t_rm(271,288), t_rm(271,288) * nu_rm(271,288),
    t_rm(277,288), t_rm(277,288) * nu_rm(277,288) ],
  Concatenation(List(FACTORS_OF_CP_CYCS,cyc->List([2..Length(cyc)],
                     i->RcwaMapping([[rc(cyc[1],288),rc(cyc[i],288)]])))),
  [ RcwaMapping([[-1,1,1]]), t, RcwaMapping([[-1,1,1]]), t,
    RcwaMapping([[-1,1,1]]), t, RcwaMapping([[-1,1,1]]), t ],
  FactorsOfCollatzPermutation{[3..15]},
  [ f1, f2, f3, t, RcwaMapping([[-1,1,1]]), t, RcwaMapping([[-1,1,1]]),
    t, RcwaMapping([[-1,1,1]]), t, RcwaMapping([[-1,1,1]]),
    f1, f2, f3, f1, f2, f3, f1, f2, f3, f1, f2, f3 ] );

#############################################################################
##
##  Class transpositions can be written as commutators:
##
##  The class transposition interchanging <r1>(<m1>) and <r2>(<m2>) is the
##  commutator of `ct1'(<r1>,<m1>,<r2>,<m2>) and `ct2'(<r1>,<m1>,<r2>,<m2>).
##
tau1 := RcwaMapping([[1,1,1],[1,1,1],[1,-2,1],[1,0,1]]);
tau2 := RcwaMapping([[1,1,1],[1,2,1],[1,0,1],[1,-3,1]]);

ct1   := function(r1,m1,r2,m2)
           return Restriction(tau1,
                              RcwaMapping([[m1,2*r1,2],[m2,2*r2-m2,2]]));
         end;
ct2   := function(r1,m1,r2,m2)
           return Restriction(tau2,
                              RcwaMapping([[m1,2*r1,2],[m2,2*r2-m2,2]]));
         end;

#############################################################################
##
##  ``Class switches'': Involutions which interchange two residue classes
##  which are not necessarily disjoint (of course there must not be a proper
##  subset relation between them!):
##
ClassSwitch := function( r1, m1, r2, m2 )

  local  cl, int, diff, lng, pos, clsp, sp, c, r, m, rti, mti, rest, i;

  cl  := List([[r1,m1],[r2,m2]],ResidueClass);
  int := Intersection(cl);
  if int = [] then return ClassTransposition(r1,m1,r2,m2); fi;
  diff := [Difference(cl[1],cl[2]),Difference(cl[2],cl[1])];
  if [] in diff then return fail; fi; # Subset relation --> no class switch!
  diff := List(diff,AsUnionOfFewClasses); lng := List(diff,Length);
  if lng[1] <> lng[2] then
    if lng[1] < lng[2] then pos := 1; else pos := 2; fi;
    for i in [1..AbsInt(lng[1]-lng[2])] do
      clsp := diff[pos][1];
      sp := [ResidueClass(Residues(clsp)[1],              2*Modulus(clsp)),
             ResidueClass(Residues(clsp)[1]+Modulus(clsp),2*Modulus(clsp))];
      diff[pos] := Union(Difference(diff[pos],[clsp]),sp);
    od;
  fi;
  lng := Maximum(lng); m := 2*lng; c := [];
  for r in [0..m-1] do
    rti := Residues(diff[r mod 2 + 1][Int(r/2)+1])[1];
    mti := Modulus (diff[r mod 2 + 1][Int(r/2)+1]);
    c[r+1] := [mti,m*rti-mti*r,m];
  od;
  rest := RcwaMapping(c);
  return Restriction(tau,rest);
end;

#############################################################################
##
##  Examples of rcwa mappings of Z^2.
##
R := Integers^2;

twice        := RcwaMapping(R,[[1,0],[0,1]],[[[[2,0],[0,2]],[0,0],1]]);
twice1       := RcwaMapping(R,[[1,0],[0,1]],[[[[2,0],[0,1]],[0,0],1]]);
twice2       := RcwaMapping(R,[[1,0],[0,1]],[[[[1,0],[0,2]],[0,0],1]]);
switch       := RcwaMapping(R,[[1,0],[0,1]],[[[[0,1],[1,0]],[0,0],1]]);
reflection   := RcwaMapping(R,[[1,0],[0,1]],[[[[-1,0],[0,-1]],[0,0],1]]);
reflection1  := RcwaMapping(R,[[1,0],[0,1]],[[[[-1,0],[0,1]],[0,0],1]]);
reflection2  := RcwaMapping(R,[[1,0],[0,1]],[[[[1,0],[0,-1]],[0,0],1]]);
transvection := RcwaMapping(R,[[1,0],[0,1]],[[[[1,1],[1,0]],[0,0],1]]);

SigmaT := RcwaMapping( R, [[1,0],[0,6]],
                          [[[0,0],[[[2,0],[0,1]],[0,0],2]],
                           [[0,1],[[[4,0],[0,3]],[0,1],2]],
                           [[0,2],[[[2,0],[0,1]],[0,0],2]],
                           [[0,3],[[[4,0],[0,3]],[0,1],2]],
                           [[0,4],[[[4,0],[0,1]],[2,0],2]],
                           [[0,5],[[[4,0],[0,3]],[0,1],2]]] );

SigmaTm := RcwaMapping( R, [[1,0],[0,6]],
                           [[[0,0],[[[2,0],[0,1]],[0,0],2]],
                            [[0,1],[[[4,0],[0,3]],[0,-1],2]],
                            [[0,2],[[[4,0],[0,1]],[2,0],2]],
                            [[0,3],[[[4,0],[0,3]],[0,-1],2]],
                            [[0,4],[[[2,0],[0,1]],[0,0],2]],
                            [[0,5],[[[4,0],[0,3]],[0,-1],2]]] );

commT_Tm := RcwaMapping( R, [[4,0],[0,9]],
                            [[[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[3,0],[0,1]],[3,1],3],
                             [[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[1,0],[0,1]],[0,-1],1],
                             [[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[2,0],[0,1]],[2,-1],1],
                             [[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[1,0],[0,3]],[-1,1],1],
                             [[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[1,0],[0,3]],[-1,1],1],
                             [[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[1,0],[0,3]],[-1,1],1],
                             [[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[1,0],[0,2]],[-2,-2],2],
                             [[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[1,0],[0,1]],[0,-1],1],
                             [[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[2,0],[0,1]],[2,-1],1],
                             [[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[1,0],[0,4]],[-3,0],4],
                             [[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[1,0],[0,4]],[-3,0],4],
                             [[[1,0],[0,1]],[0,0],1],
                             [[[4,0],[0,1]],[3,0],1],
                             [[[1,0],[0,4]],[-3,0],4]] );

#############################################################################
##
#E  examples.g . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here