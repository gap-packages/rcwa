#############################################################################
##
#W  examples.g                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains the rcwa mappings used in the examples in the manual,
##  as well as a number of other interesting or illustrative examples.
##

# First of all a few useful abbreviations.

rc := function(r,m) return ResidueClass(DefaultRing(m),m,r); end;
md := f -> [Multiplier(f),Divisor(f)];

#############################################################################
##
##  Some basic `building blocks'.
##
nu  := RcwaMapping([[ 1, 1, 1]]); SetName(nu,"nu");
t   := RcwaMapping([[-1, 0, 1]]); SetName(t,"t");
tau := RcwaMapping([[1,1,1],[1,-1,1]]);

# Class shifts, class reflections and class transpositions given as images of
# these basic generators under restriction monomorphisms.

nu_rm := function(r,m) return Restriction(nu,RcwaMapping([[m,r,1]])); end;
t_rm  := function(r,m) return Restriction(t, RcwaMapping([[m,r,1]])); end;
ct    := function(r1,m1,r2,m2)
           return Restriction(tau,RcwaMapping([[m1,2*r1,2],[m2,2*r2-m2,2]]));
         end;

# A class transposition ct(r1,m1,r2,m2) is the commutator of the following
# mappings ct1(r1,m1,r2,m2) und ct2(r1,m1,r2,m2):

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

# `Class switches': Involutions which interchange two residue classes which
# are not necessarily disjoint (of course there must not be a proper subset
# relation between them!):

cs := function(r1,m1,r2,m2)

  local  cl, int, diff, lng, pos, clsp, sp, c, r, m, rti, mti, rest, i;

  cl := [rc(r1,m1),rc(r2,m2)];
  int := Intersection(cl);
  if int = [] then return ct(r1,m1,r2,m2); fi;
  diff := [Difference(cl[1],cl[2]),Difference(cl[2],cl[1])];
  if [] in diff then return fail; fi; # Subset relation --> no class switch!
  diff := List(diff,AsUnionOfFewClasses); lng := List(diff,Length);
  if lng[1] <> lng[2] then
    if lng[1] < lng[2] then pos := 1; else pos := 2; fi;
    for i in [1..AbsInt(lng[1]-lng[2])] do
      clsp := diff[pos][1];
      sp   := [rc(Residues(clsp)[1],              2*Modulus(clsp)),
               rc(Residues(clsp)[1]+Modulus(clsp),2*Modulus(clsp))];
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
##  `Three involutions whose product has coprime multiplier and divisor'
##
f1 := RcwaMapping([[rc(1,6),rc(0, 8)],[rc(5,6),rc(4, 8)]]); SetName(f1,"f1");
f2 := RcwaMapping([[rc(1,6),rc(0, 4)],[rc(5,6),rc(2, 4)]]); SetName(f2,"f2");
f3 := RcwaMapping([[rc(2,6),rc(1,12)],[rc(4,6),rc(7,12)]]); SetName(f3,"f3");

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

# Two mappings with non-balanced commutator.

c1 := Restriction(RcwaMapping([[2,0,3],[4,-1,3],[4,1,3]]),
                  RcwaMapping([[2,0,1]]));
c2 := RcwaMapping([[1,0,2,],[2,1,1],[1,-1,1],[2,1,1]]);
SetName(c1,"c1"); SetName(c2,"c2");

#############################################################################
##
##  `An rcwa mapping which seems to be contracting, but very slow'
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
##  `The examples by Matthews and Leigh'
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
##  `An abelian rcwa group over a polynomial ring'
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
##  `Exploring the structure of a wild rcwa group'
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
##  `A wild rcwa mapping which has only finite cycles'
##
kappa := RcwaMapping([[1,0,1],[1,0,1],[3,2,2],[1,-1,1],
                      [2,0,1],[1,0,1],[3,2,2],[1,-1,1],
                      [1,1,3],[1,0,1],[3,2,2],[2,-2,1]]);
SetName(kappa,"kappa");

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
# mapping `kappatilde' above, apparently one `chaotically behaving' infinite
# cycle which has positive density (apparently 11/48) as a subset of Z.

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
# apparently has only one(!) cycle, traversing the set (0(4) U 1(6) U 5(12)
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
##  `An rcwa representation of a small group'
##
r := RcwaMapping([[1,0,1],[1,1,1],[3, -3,1],
                  [1,0,3],[1,1,1],[3, -3,1],
                  [1,0,1],[1,1,1],[3, -3,1]]); SetName(r,"r");
s := RcwaMapping([[1,0,1],[1,1,1],[3,  6,1],
                  [1,0,3],[1,1,1],[3,  6,1],
                  [1,0,1],[1,1,1],[3,-21,1]]); SetName(s,"s");

#############################################################################
##
##  `An rcwa representation of the symmetric group on 10 point'
##
a := RcwaMapping([[3,0,2],[3, 1,4],[3,0,2],[3,-1,4]]); SetName(a,"a");
b := RcwaMapping([[3,0,2],[3,13,4],[3,0,2],[3,-1,4]]); SetName(b,"b");
c := RcwaMapping([[3,0,2],[3, 1,4],[3,0,2],[3,11,4]]); SetName(c,"c");

ab := Comm(a,b); SetName(ab,"[a,b]");
ac := Comm(a,c); SetName(ac,"[a,c]");
bc := Comm(b,c); SetName(bc,"[b,c]");

# Two rcwa mappings of orders 7 and 12, respectively, which have isomorphic
# transition graphs for modulus 6 and generate the infinite tame group we
# have looked at in the example we gave in the chapter about rcwa groups
# for the use of `RespectedClassPartition'.

g := RcwaMapping([[2,2,1],[1, 4,1],[1,0,2],[2,2,1],[1,-4,1],[1,-2,1]]);
h := RcwaMapping([[2,2,1],[1,-2,1],[1,0,2],[2,2,1],[1,-1,1],[1, 1,1]]);
SetName(g,"g"); SetName(h,"h");

# A factorization of `a' (see above) into two balanced mappings,
# where one of them is an involution.

a_2 := RcwaMapping([[rc(1,2),rc(36,72)]]); a_1 := a/a_2;
SetName(a_1,"a_1"); SetName(a_2,"a_2");

#############################################################################
##
##  `Some examples over (semi)localizations of the integers'
##
a2  := RcwaMapping(Z_pi(2),    ShallowCopy(Coefficients(a)));

a23 := RcwaMapping(Z_pi([2,3]),ShallowCopy(Coefficients(a)));
b23 := RcwaMapping(Z_pi([2,3]),ShallowCopy(Coefficients(b)));
c23 := RcwaMapping(Z_pi([2,3]),ShallowCopy(Coefficients(c)));

ab23 := Comm(a23,b23); ac23 := Comm(a23,c23);

v := RcwaMapping([[6,0,1],[1,-7,2],[6,0,1],[1,-1,1],
                  [6,0,1],[1, 1,2],[6,0,1],[1,-1,1]]);

v2 := RcwaMapping(Z_pi(2),ShallowCopy(Coefficients(v)));
w2 := RcwaMapping(Z_pi(2),[[1,0,2],[2,-1,1],[1,1,1],[2,-1,1]]);
SetName(v,"v"); SetName(v2,"v2"); SetName(w2,"w2");

v2w2 := Comm(v2,w2); SetName(v2w2,"[v2,w2]");

#############################################################################
##
##  `Twisting 257-cycles into an rcwa mapping with modulus 32'
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
##  `The behaviour of the moduli of powers'
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
##  `Images and preimages under the Collatz mapping'
##
T := RcwaMapping([[1,0,2],[3,1,2]]); SetName(T,"T");

T5 := RcwaMapping([[1,0,2],[5,-1,2]]); SetName(T5,"T5");

#############################################################################
##
##  `Replacing the Collatz mapping by conjugates'
##
##  (All mappings used in this example have already been defined above.)

#############################################################################
##
##  The Venturini examples.
##
V1 := t -> RcwaMapping([[2500,6     ,6],[t,  -t+4,2],[1,16,6],
                        [t   ,-3*t+4,2],[t,-4*t+4,2],[1,13,6]]);

V2 := function ( k, p, t )

        local  c, r;

        if not IsSubset(PositiveIntegers,[k,p,t])
          or t < 1 or t >= p or Gcd(p,t) <> 1 then return fail;
        fi;
        c := [[p^(k-1),1,1]];
        for r in [1..p-1] do c[r+1] := [t,r*(p-t),p]; od;
        return RcwaMapping(c);        
      end;

V3 := t -> RcwaMapping([[ 1, 0,4],[1,  1,2],[20,    -40,1],[1,-3,8],
                        [20,48,1],[3,-13,2],[ t,-6*t+64,4],[1, 1,8]]);

V4 := RcwaMapping([[9, 1,1],[  1,  32,3],[1,-2,3],
                   [1, 3,1],[100,-364,9],[1,-5,3],
                   [1,-6,1],[100,-637,9],[1,-8,3]]);

V5 := RcwaMapping([[1,0,6],[2,16,3],[3,11,1],[1,-3,6],[1,-4,1],[1,9,2]]);

V6 := RcwaMapping([[1,  4,2],[1,  3,2],[ 1,  2, 2],[ 1,  1, 2],[ 1,  0, 2],
                   [5,-17,2],[5,-22,2],[17,-39,10],[17,-56,10],[17,-73,10]]);

V7 := RcwaMapping([[1,0,3],[2,-2,3],[5,-4,3],[4,0,3],[5,-8,3],[4,-2,3]]);

V8 := RcwaMapping([[1,0,3],[1,-1,3],[5,5,3],[3,5,2],[3,2,2],[3,-1,2]]);

#############################################################################
##
#E  examples.g . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here