#############################################################################
##
#W  resclass.gd                GAP4 Package `RCWA'                Stefan Kohl
##
#H  @(#)$Id$
##
#Y  Copyright (C) 2002 by Stefan Kohl, Mathematisches Institut B,
#Y  Universit\"at Stuttgart, Germany
##
##  This file contains declarations needed for dealing with unions of
##  residue classes and finite sets.
##
Revision.resclass_gd :=
  "@(#)$Id$";

#############################################################################
##
#C  IsUnionOfResidueClasses . . . . unions of residue classes and finite sets
##
##  The category of all unions of residue classes and finite sets.
##
DeclareCategory( "IsUnionOfResidueClasses", IsListOrCollection );

#############################################################################
##
#C  IsUnionOfResidueClassesOfZ . .  unions of residue classes and finite sets
##
##  The category of unions of residue classes of the integers and finite sets
##  of integers.
##
DeclareCategory( "IsUnionOfResidueClassesOfZ", IsListOrCollection );

#############################################################################
##
#C  IsUnionOfResidueClassesOfZ_pi . unions of residue classes and finite sets
##
##  The category of unions of residue classes of some ring $\Z_\pi$ and
##  finite subsets of of this ring. 
##
DeclareCategory( "IsUnionOfResidueClassesOfZ_pi", IsListOrCollection );

#############################################################################
##
#C  IsUnionOfResidueClassesOfZorZ_pi . unions of res. classes and finite sets
##
##  The union of the categories `IsUnionOfResidueClassesOfZ' and
##  `IsUnionOfResidueClassesOfZ_pi'.
##
DeclareCategory( "IsUnionOfResidueClassesOfZorZ_pi", IsListOrCollection );

#############################################################################
##
#C  IsUnionOfResidueClassesOfGFqx . . .  unions of res. classes and fin. sets
##
##  The category of unions of residue classes of some ring GF($q$)[$x$] and
##  finite subsets of of this ring. 
##
DeclareCategory( "IsUnionOfResidueClassesOfGFqx", IsListOrCollection );

#############################################################################
##
#F  ResidueClassUnionsFamily( <R> ) . family of all residue class unions of R
##
DeclareGlobalFunction( "ResidueClassUnionsFamily" );

#############################################################################
##
#V  ZResidueClassUnionsFamily . . . . .  family of all res. class unions of Z
##
DeclareGlobalVariable( "ZResidueClassUnionsFamily" );

#############################################################################
##
#F  Z_piResidueClassUnionsFamily( <R> )
##
##  Family of unions of residue classes of $\Z_\pi$ and finite subsets of
##  this ring, where the set $\pi$ is given by the list <primes>.
##
DeclareGlobalFunction( "Z_piResidueClassUnionsFamily" );

#############################################################################
##
#F  GFqxResidueClassUnionsFamily( <R> )
##
##  Family of unions of residue classes of the ring $R$ = GF($q$)[$x$] and
##  finite subsets of this ring.
##
DeclareGlobalFunction( "GFqxResidueClassUnionsFamily" );

#############################################################################
##
#R  IsResidueClassUnionSparseRep . . .  `sparse' rep. of residue class unions
##
##  Representation of unions of residue classes of the integers, a
##  semilocalization $\Z_\pi$ of the integers or a univariate polynomial ring
##  GF($q$)[$x$] over a finite field.
## 
##  The component <m> stores the common modulus, <r> is the list of class
##  representatives and <included> resp. <excluded> are lists of single
##  elements added to resp. subtracted from the union of classes.
##
DeclareRepresentation( "IsResidueClassUnionSparseRep", 
                       IsComponentObjectRep and IsAttributeStoringRep, 
                       [ "m", "r", "included", "excluded" ] );

#############################################################################
##
#O  ResidueClassUnionCons( <R>, <m>, <r>, <included>, <excluded> )
##
##  Constructor for unions of residue classes +/- finite sets of elements.
##
##  Constructs the union of the residue classes <r>[i] ( mod <m> ) of the
##  ring <R>, where <included> resp. <excluded> denote lists of single
##  elements which should be included in resp. excluded from the union.
##
DeclareConstructor( "ResidueClassUnionCons",
                    [ IsUnionOfResidueClasses, IsRing, IsRingElement,
                      IsList, IsList, IsList ] );

#############################################################################
##
#F  ResidueClass( <R>, <m>, <r> ) . . . . . . . . . . .  single residue class
##
##  The residue class <r> ( mod <m> ) of the ring <R>.
##
DeclareGlobalFunction( "ResidueClass" );

#############################################################################
##
#F  ResidueClassUnion( <R>, <m>, <r> ) . . . . . . . union of residue classes
#F  ResidueClassUnion( <R>, <m>, <r>, <included>, <excluded> )
##
##  Calls `ResidueClassUnionCons'.
##  For a description of the arguments, see there.
##
DeclareGlobalFunction( "ResidueClassUnion" );

#############################################################################
##
#O  Residues( <U> ) . . . . . . . . . . . . . residues of residue class union
##
DeclareOperation( "Residues", [ IsUnionOfResidueClasses ] );

#############################################################################
##
#O  IncludedElements( <U> ) . included single elements of residue class union
##
DeclareOperation( "IncludedElements", [ IsUnionOfResidueClasses ] );

#############################################################################
##
#O  ExcludedElements( <U> ) . excluded single elements of residue class union
##
DeclareOperation( "ExcludedElements", [ IsUnionOfResidueClasses ] );

#############################################################################
##
#O  Complement( <U> ) . . . . . . . . . . . complement of residue class union
##
if   not IsBound( Complement ) # In case CRISP is not loaded.
then DeclareOperation( "Complement", [ IsObject ] ); fi;

#############################################################################
##
#R  IsResidueClassUnionsIteratorRep( <U> ) . . . . .  iterator representation
##
DeclareRepresentation( "IsResidueClassUnionsIteratorRep",
                       IsComponentObjectRep,
                       [ "structure", "counter", "element", "classpos" ] );

#############################################################################
##
#E  resclass.gd . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
