#############################################################################
##
#W  banner.g                 GAP4 Package `RCWA'                  Stefan Kohl
##
#H  @(#)$Id$
##

if not CompareVersionNumbers( VERSION, "4r4" ) and not QUIET and BANNER then
  Print("\nLoading RCWA ",PACKAGES_VERSIONS.rcwa);
  Print(" ([R]esidue [C]lass-[W]ise [A]ffine mappings and groups)");
  Print("\nby Stefan Kohl, kohl@mathematik.uni-stuttgart.de\n\n");
fi;

#############################################################################
##
#E  banner.g . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here
