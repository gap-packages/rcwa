#############################################################################
##
#W  z_pi.gd                  GAP4 Package `RCWA'                  Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains the declaration part for the semilocalizations Z_pi of
##  the ring of integers.
##
Revision.z_pi_gd :=
  "@(#)$Id$";

#############################################################################
##
#O  Z_piCons( <pi> ) . . . . . . . . semilocalization Z_pi for prime set <pi>
##
DeclareConstructor( "Z_piCons", [ IsRing, IsList ] );

#############################################################################
##
#F  Z_pi( <pi> ) . . . . . . . . . . semilocalization Z_pi for prime set <pi>
##
DeclareGlobalFunction( "Z_pi" );

#############################################################################
##
#P  IsZ_pi( <R> ) . . . . . . . . . . . . . . . . . . . . . . . . . . .  Z_pi
##
DeclareProperty( "IsZ_pi", IsEuclideanRing );

#############################################################################
##
#F  NoninvertiblePrimes( <R> ) . . the set of non-inv. primes in the ring <R>
##
DeclareAttribute( "NoninvertiblePrimes", IsRing );

#############################################################################
##
#E  z_pi.gd . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here