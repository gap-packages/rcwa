#############################################################################
##
#W  rcwamono.gd                GAP4 Package `RCWA'                Stefan Kohl
##
##  This file contains declarations of functions, operations etc. for
##  computing with rcwa monoids.
##
##  See the definitions given in the file rcwamap.gd.
##
#############################################################################

#############################################################################
##
#C  IsRcwaMonoidOverZ . . . . . . . . . . . . . . . . . . rcwa monoids over Z
#C  IsRcwaMonoidOverZxZ . . . . . . . . . . . . . . . . rcwa monoids over Z^2
#C  IsRcwaMonoidOverZ_pi  . . . . . . . . . . . . .  rcwa monoids over Z_(pi)
#C  IsRcwaMonoidOverGFqx  . . . . . . . . . . . .  rcwa monoids over GF(q)[x]
#C  IsRcwaMonoidOverZOrZ_pi . . . . . . . . . . rcwa monoids over Z or Z_(pi)
##
##  The category of all rcwa monoids over Z, over Z^2, over semilocalizations
##  of Z or over polynomial rings in one variable over a finite field,
##  respectively. The category `IsRcwaMonoidOverZOrZ_pi' is the union of
##  `IsRcwaMonoidOverZ' and `IsRcwaMonoidOverZ_pi'.
##
DeclareSynonym( "IsRcwaMonoidOverZ",
                 CategoryCollections(IsRcwaMappingOfZ) and IsMonoid );
DeclareSynonym( "IsRcwaMonoidOverZxZ",
                 CategoryCollections(IsRcwaMappingOfZxZ) and IsMonoid );
DeclareSynonym( "IsRcwaMonoidOverZ_pi",
                 CategoryCollections(IsRcwaMappingOfZ_pi) and IsMonoid );
DeclareSynonym( "IsRcwaMonoidOverGFqx",
                 CategoryCollections(IsRcwaMappingOfGFqx) and IsMonoid );
DeclareSynonym( "IsRcwaMonoidOverZOrZ_pi",
                 CategoryCollections(IsRcwaMappingOfZOrZ_pi) and IsMonoid );

#############################################################################
##
#O  RcwaCons( <R> ) . . . . . . . . . . . . . . . . . .  Rcwa( R ) for ring R
#F  Rcwa( <R> )
##
##  The monoid formed by all rcwa mappings of <R>.
##
DeclareConstructor( "RcwaCons", [ IsRcwaMonoid, IsDomain ] );
DeclareGlobalFunction( "Rcwa" );

#############################################################################
##
#P  IsNaturalRcwa( <M> ) . . . . . . . . . . . . . . . . . . . . .  Rcwa( R )
##
DeclareCategory( "IsNaturalRcwa", IsRcwaMonoid );

#############################################################################
##
#A  ModulusOfRcwaMonoid( <M> ) . . . . . . . . modulus of the rcwa monoid <M>
##
##  We define the *modulus* of an rcwa monoid by the lcm of the moduli of its
##  elements in case such an lcm exists, and by 0 otherwise. 
##
DeclareAttribute( "ModulusOfRcwaMonoid", IsRcwaMonoid );

#############################################################################
##
#O  Ball( <M>, <f>, <r> )    ball of radius <r> around the element <f> of <M>
#O  Ball( <M>, <p>, <r>, <act> )   "    the point <p> under the action of <M>
#O  Ball( <M>, <p>, <r> ) . . .  as above, where <act> defaults to `OnPoints'
#O  RestrictedBall( <M>, <f>, <r>, <modulusbound> ) . . . . "restricted" ball
#O  RestrictedBall( <M>, <p>, <r>, <act>, <bound> ) . . . . . . . . .  (dito)
#O  RestrictedBall( <M>, <p>, <r>, <bound> )  . . . . . . . . . . . .  (dito)
#O  RestrictedBall( <M>, <f>, <r>, <bounds> ) . . . . . . . . . . . .  (dito)
##
##  The first variant returns the ball of radius <r> about the element <f>
##  of <M>.
##
##  The second variant returns the ball of radius <r> about the point <p>
##  under the action of <M>.
##
##  The third variant is the same as the second --
##  <act> defaults to `OnPoints'.
##
##  The fourth variant does the same as the first except that it stops
##  where extending the ball would yield elements whose moduli exceed the
##  bound <modulusbound>.
##
##  The fifth variant does the same as the second except that it stops
##  where further extending the ball would yield points which exceed the
##  bound <bound> in absolute value. If the points are tuples, then the
##  bound applies to all coordinates.
##
##  The sixth variant is the fifth -- <act> defaults to `OnPoints'.
##
##  All balls are understood w.r.t. the stored generators of the monoid <M>,
##  respectively w.r.t. the stored generators and their inverses if <M> is
##  actually a group.
##
##  An option `Spheres' is recognized. If set, the returned ball is split
##  into a list of spheres.
##
DeclareOperation( "Ball", [ IsMonoid, IsObject, IsInt ] );
DeclareOperation( "Ball", [ IsMonoid, IsObject, IsInt, IsFunction ] );
DeclareOperation( "RestrictedBall",
                  [ IsMonoid, IsObject, IsObject, IsObject ] );
DeclareOperation( "RestrictedBall",
                  [ IsMonoid, IsObject, IsObject, IsObject, IsObject ] );

#############################################################################
##
#O  ShortOrbits( <G>, <S>, <maxlng> ) . . . .  short orbits of rcwa group <G>
#O  ShortOrbits( <G>, <S>, <maxlng>, <maxn> ) . dito, with upper bound <maxn>
#O  ShortOrbits( <M>, <S>, <maxlng> ) short forward orbits of rcwa monoid <M>
##
##  In the first case, this operation returns a list of all finite orbits of
##  the rcwa group <G> of length <= <maxlng>, which intersect nontrivially
##  with the set <S>.
##  In the second case, it returns a list of all such orbits which do not
##  contain a point larger than <maxn>.
##  In the third case, it returns a list of all finite forward orbits with
##  starting point within the set <S>, of length <= <maxlng>.
##
DeclareOperation( "ShortOrbits", [ IsMonoid, IsListOrCollection, IsInt ] );
DeclareOperation( "ShortOrbits", [ IsMonoid, IsListOrCollection, IsInt,
                                   IsInt ] );

#############################################################################
##
#E  rcwamono.gd . . . . . . . . . . . . . . . . . . . . . . . . . . ends here