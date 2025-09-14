#############################################################################
##
#W  init.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
##  Read the declaration part of the package.
##
#############################################################################

# introducing globally the NC versions of PreImages* function for
# compatibility with older GAP version which do not provide them
if not IsBound( PreImagesNC ) then 
    BindGlobal( "PreImagesNC", PreImages ); 
fi; 
if not IsBound( PreImagesElmNC ) then 
    BindGlobal( "PreImagesElmNC", PreImagesElm ); 
fi; 
if not IsBound( PreImagesSetNC ) then 
    BindGlobal( "PreImagesSetNC", PreImagesSet ); 
fi; 
if not IsBound( PreImagesRepresentativeNC ) then 
    BindGlobal( "PreImagesRepresentativeNC", PreImagesRepresentative ); 
fi; 

#############################################################################

ReadPackage( "rcwa", "lib/rcwamap.gd" );
ReadPackage( "rcwa", "lib/rcwamono.gd" );
ReadPackage( "rcwa", "lib/rcwagrp.gd" );

#############################################################################
##
#E  init.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
