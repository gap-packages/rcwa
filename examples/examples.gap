#############################################################################
##
#W  examples.gap               GAP4 Package `RCWA'                Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains the rcwa mappings used in the examples in the manual.
##

# Rcwa mappings used in the Collatz problem example.

T := RcwaMapping([[1,0,2],[3,1,2]]);
a := RcwaMapping([[3,0,2],[3,1,4],[3,0,2],[3,-1,4]]);
u := RcwaMapping([[3,0,5],[9,1,5],[3,-1,5],[9,-2,5],[9,4,5]]);

# Rcwa mappings used in the Syl_3(S_9) - example.

r := RcwaMapping([[1,0,1],[1,1,1],[3, -3,1],
                  [1,0,3],[1,1,1],[3, -3,1],
                  [1,0,1],[1,1,1],[3, -3,1]]);
s := RcwaMapping([[1,0,1],[1,1,1],[3,  6,1],
                  [1,0,3],[1,1,1],[3,  6,1],
                  [1,0,1],[1,1,1],[3,-21,1]]);


# Rcwa mappings used in the S_10 - example.

a := RcwaMapping([[3,0,2],[3, 1,4],[3,0,2],[3,-1,4]]);
b := RcwaMapping([[3,0,2],[3,13,4],[3,0,2],[3,-1,4]]);
c := RcwaMapping([[3,0,2],[3, 1,4],[3,0,2],[3,11,4]]);

ab := Comm(a,b);
ac := Comm(a,c);
bc := Comm(b,c);


# Rcwa mapping used in the 257-cycle example.

x := RcwaMapping([[ 16,  2,  1], [ 16, 18,  1],
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


# Rcwa mappings used in the example of two mappings with
# isomorphic graphs but different orders.

g := RcwaMapping([[2,2,1],[1, 4,1],[1,0,2],[2,2,1],[1,-4,1],[1,-2,1]]);
h := RcwaMapping([[2,2,1],[1,-2,1],[1,0,2],[2,2,1],[1,-1,1],[1, 1,1]]);

# Rcwa mappings used in the free abelian normal subgroup example.

v := RcwaMapping([[-1,2,1],[1,-1,1],[1,-1,1]]);
w := RcwaMapping([[-1,3,1],[1,-1,1],[1,-1,1],[1,-1,1]]);

# Rcwa mappings used in the ``behaviour of the moduli of powers'' - example.

z := RcwaMapping([[2,  1, 1],[1,  1,1],[2, -1,1],[2, -2,1],
                  [1,  6, 2],[1,  1,1],[1, -6,2],[2,  5,1],
                  [1,  6, 2],[1,  1,1],[1,  1,1],[2, -5,1],
                  [1,  0, 1],[1, -4,1],[1,  0,1],[2,-10,1]]);

e1 := RcwaMapping([[1,4,1],[2,0,1],[1,0,2],[2,0,1]]);
e2 := RcwaMapping([[1,4,1],[2,0,1],[1,0,2],[1,0,1],
                   [1,4,1],[2,0,1],[1,0,1],[1,0,1]]);

#############################################################################
##
#E  examples.gap . . . . . . . . . . . . . . . . . . . . . . . . .  ends here