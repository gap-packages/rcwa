#############################################################################
##
#W  compat44.g                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains the 4.4 compatibility code.
##
Revision.compat44_g :=
  "@(#)$Id$";

BindGlobal( "PadicValuation",

  function ( rat, p )

    local  a1, a2;

    if rat = 0 then return infinity; fi;
    a1 := AbsInt( NumeratorRat( rat ) );
    a2 := DenominatorRat( rat );
    a1 := Length( Filtered( FactorsInt( a1 ), x -> x = p ) );
    a2 := Length( Filtered( FactorsInt( a2 ), x -> x = p ) );
    return a1 - a2;
  end );

DeclareAttribute( "EpimorphismFromFreeGroup", IsGroup );

InstallMethod( EpimorphismFromFreeGroup,
               "general", true, [ IsGroup and HasGeneratorsOfGroup ], 0,

  function( G )

    local  F, str;

    str := ValueOption("names");
    if    IsList(str) and ForAll(str,IsString)
      and Length(str) = Length(GeneratorsOfGroup(G))
    then F:=FreeGroup(str);
    else if not IsString(str) then str := "x"; fi;
         F:=FreeGroup(Length(GeneratorsOfGroup(G)),str);
    fi;
    return GroupHomomorphismByImagesNC(F,G,GeneratorsOfGroup(F),
                                           GeneratorsOfGroup(G));
  end );

#############################################################################
##
#E  compat44.g . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here