#############################################################################
##
#W  rcwalib.gi                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains a ``basic groups library'' for integral rcwa groups.
##  Presently, here are only ``trivial representations'' of some groups from
##  the library.
##
Revision.rcwalib_gi :=
  "@(#)$Id$";

#############################################################################
##
#M  CyclicGroupCons( IsIntegralRcwaGroup, <n> )
##
InstallMethod( CyclicGroupCons,
               "RCWA: integral rcwa group with size",
               true, [ IsIntegralRcwaGroup and IsFinite, IsPosInt ], 0,

  function( filter, n )

    return IntegralRcwaGroupByPermGroup( CyclicGroup( IsPermGroup, n ) );
  end );

#############################################################################
##
#M  AbelianGroupCons( IsIntegralRcwaGroup, <n> )
##
InstallMethod( AbelianGroupCons,
               "RCWA: integral rcwa group with abelian invariants",
               true, [ IsIntegralRcwaGroup and IsFinite, IsList ], 0,

  function( filter, abinv )

    return IntegralRcwaGroupByPermGroup(
             AbelianGroup( IsPermGroup, abinv ) );
  end );

#############################################################################
##
#M  ElementaryAbelianGroupCons( IsIntegralRcwaGroup, <n> )
##
InstallMethod( ElementaryAbelianGroupCons,
               "RCWA: integral rcwa group with size",
               true, [ IsIntegralRcwaGroup and IsFinite, IsPosInt ], 0,

  function( filter, n )

    return IntegralRcwaGroupByPermGroup(
             ElementaryAbelianGroup( IsPermGroup, n ) );
  end );

#############################################################################
##
#M  ExtraspecialGroupCons( IsIntegralRcwaGroup, <order>, <exp> )
##
InstallMethod( ExtraspecialGroupCons,
               "RCWA: integral rcwa group with degree and finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite,
                       IsPosInt, IsPosInt ], 0,

  function( filter, order, exp )

    return IntegralRcwaGroupByPermGroup( Image( IsomorphismPermGroup(
             ExtraspecialGroup( order, exp ) ) ) );
  end );

#############################################################################
##
#M  DihedralGroupCons( IsIntegralRcwaGroup, <n> )
##
InstallMethod( DihedralGroupCons,
               "RCWA: integral rcwa group with size",
               true, [ IsIntegralRcwaGroup and IsFinite, IsPosInt ], 0,

  function( filter, n )

    return IntegralRcwaGroupByPermGroup( DihedralGroup( IsPermGroup, n ) );
  end );

#############################################################################
##
#M  SymmetricGroupCons( IsIntegralRcwaGroup, <n> )
##
InstallMethod( SymmetricGroupCons,
               "RCWA: integral rcwa group by degree",
               true, [ IsIntegralRcwaGroup and IsFinite, IsPosInt ], 0,

  function( filter, n )

    return IntegralRcwaGroupByPermGroup( SymmetricGroup( n ) );
  end );

#############################################################################
##
#M  AlternatingGroupCons( IsIntegralRcwaGroup, <n> )
##
InstallMethod( AlternatingGroupCons,
               "RCWA: integral rcwa group by degree",
               true, [ IsIntegralRcwaGroup and IsFinite, IsPosInt ], 0,

  function( filter, n )

    return IntegralRcwaGroupByPermGroup( AlternatingGroup( n ) );
  end );

#############################################################################
##
#M  GeneralLinearGroupCons( IsIntegralRcwaGroup, <d>, <q> )
##
InstallMethod( GeneralLinearGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup, IsPosInt, IsField and IsFinite ],
               0,

  function( filter, d, F )

    return IntegralRcwaGroupByPermGroup(
             Image( IsomorphismPermGroup( GL ( d, Size( F ) ) ) ) );
  end );

#############################################################################
##
#M  SpecialLinearGroupCons( IsIntegralRcwaGroup, <d>, <q> )
##
InstallMethod( SpecialLinearGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup, IsPosInt, IsField and IsFinite ],
               0,

  function( filter, d, F )

    return IntegralRcwaGroupByPermGroup(
             Image(IsomorphismPermGroup( SL( d, Size( F ) ) ) ) );
  end );

#############################################################################
##
#M  ProjectiveGeneralLinearGroupCons( IsIntegralRcwaGroup, <d>, <q> )
##
InstallMethod( ProjectiveGeneralLinearGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite,
                       IsPosInt, IsPosInt ], 0,

  function( filter, d, q )

    return IntegralRcwaGroupByPermGroup( PGL( d, q ) );
  end );

#############################################################################
##
#M  ProjectiveSpecialLinearGroupCons( IsIntegralRcwaGroup, <d>, <q> )
##
InstallMethod( ProjectiveSpecialLinearGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite,
                       IsPosInt, IsPosInt ], 0,

  function( filter, d, q )

    return IntegralRcwaGroupByPermGroup( PSL( d, q ) );
  end );

#############################################################################
##
#M  GeneralOrthogonalGroupCons( IsIntegralRcwaGroup, <e>, <d>, <q> )
##
InstallMethod( GeneralOrthogonalGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite,
                       IsPosInt, IsPosInt, IsPosInt ], 0,

  function( filter, e, d, q )

    return IntegralRcwaGroupByPermGroup(
             Image( IsomorphismPermGroup( GO( e, d, q ) ) ) );
  end );

#############################################################################
##
#M  SpecialOrthogonalGroupCons( IsIntegralRcwaGroup, <e>, <d>, <q> )
##
InstallMethod( SpecialOrthogonalGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite,
                       IsPosInt, IsPosInt, IsPosInt ], 0,

  function( filter, e, d, q )

    return IntegralRcwaGroupByPermGroup(
             Image( IsomorphismPermGroup( SO( e, d, q ) ) ) );
  end );

#############################################################################
##
#M  GeneralUnitaryGroupCons( IsIntegralRcwaGroup, <d>, <q> )
##
InstallMethod( GeneralUnitaryGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite,
                       IsPosInt, IsPosInt ], 0,

  function( filter, d, q )

    return IntegralRcwaGroupByPermGroup(
             Image( IsomorphismPermGroup( GU( d, q ) ) ) );
  end );

#############################################################################
##
#M  SpecialUnitaryGroupCons( IsIntegralRcwaGroup, <d>, <q> )
##
InstallMethod( SpecialUnitaryGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite,
                       IsPosInt, IsPosInt ], 0,

  function( filter, d, q )

    return IntegralRcwaGroupByPermGroup(
             Image(IsomorphismPermGroup( SU( d, q ) ) ) );
  end );

#############################################################################
##
#M  ProjectiveGeneralUnitaryGroupCons( IsIntegralRcwaGroup, <d>, <q> )
##
InstallMethod( ProjectiveGeneralUnitaryGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite,
                       IsPosInt, IsPosInt ], 0,

  function( filter, d, q )

    return IntegralRcwaGroupByPermGroup( PGU( d, q ) );
  end );

#############################################################################
##
#M  ProjectiveSpecialUnitaryGroupCons( IsIntegralRcwaGroup, <d>, <q> )
##
InstallMethod( ProjectiveSpecialUnitaryGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite,
                       IsPosInt, IsPosInt ], 0,

  function( filter, d, q )

    return IntegralRcwaGroupByPermGroup( PSU( d, q ) );
  end );

#############################################################################
##
#M  SymplecticGroupCons( IsIntegralRcwaGroup, <d>, <q> )
##
InstallMethod( SymplecticGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite,
                       IsPosInt, IsPosInt ], 0,

  function( filter, d, q )

    return IntegralRcwaGroupByPermGroup(
             Image( IsomorphismPermGroup( Sp( d, q ) ) ) );
  end );

#############################################################################
##
#M  ProjectiveSymplecticGroupCons( IsIntegralRcwaGroup, <d>, <q> )
##
InstallMethod( ProjectiveSymplecticGroupCons,
               "RCWA: integral rcwa group by degree and finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite,
                       IsPosInt, IsPosInt ], 0,

  function( filter, d, q )

    return IntegralRcwaGroupByPermGroup( PSP( d, q ) );
  end );

#############################################################################
##
#M  MathieuGroupCons( IsIntegralRcwaGroup, <n> )
##
InstallMethod( MathieuGroupCons,
               "RCWA: integral rcwa group by degree",
               true, [ IsIntegralRcwaGroup and IsFinite, IsPosInt ], 0,

  function( filter, n )

    return IntegralRcwaGroupByPermGroup( MathieuGroup( n ) );
  end );

#############################################################################
##
#M  SuzukiGroupCons( IsIntegralRcwaGroup, <q> )
##
InstallMethod( SuzukiGroupCons,
               "RCWA: integral rcwa group by finite field size",
               true, [ IsIntegralRcwaGroup and IsFinite, IsPosInt ], 0,

  function( filter, q )

    return IntegralRcwaGroupByPermGroup( Sz( IsPermGroup, q ) );
  end );

#############################################################################
##
#E  rcwalib.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here

