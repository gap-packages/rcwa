                                                                                                                                                                                                                                                                                  #############################################################################
##
#W  init.g                  GAP4 Package `RCWA'                   Stefan Kohl
##
##  Read the declaration part of the package.
##
#############################################################################

#I introducing globally the NC versions of PreImages...  
if not IsBound( PreImagesElmNC ) then 
    BindGlobal( "PreImagesElmNC", PreImagesElm ); 
fi; 
if not IsBound( PreImagesSetNC ) then 
    BindGlobal( "PreImagesSetNC", PreImagesSet ); 
fi; 
if not IsBound( PreImagesRepresentativeNC ) then 
    BindGlobal( "PreImagesRepresentativeNC", PreImagesRepresentative ); 
fi; 

ReadPackage( "rcwa", "lib/rcwamap.gd" );
ReadPackage( "rcwa", "lib/rcwamono.gd" );
ReadPackage( "rcwa", "lib/rcwagrp.gd" );

#############################################################################
##
#E  init.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
