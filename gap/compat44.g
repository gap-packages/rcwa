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
