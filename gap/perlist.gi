#############################################################################
##
#W  perlist.gi                GAP4 Package `RCWA'                 Stefan Kohl
##
#H  @(#)$Id$
##
##  This file contains methods dealing with the action of rcwa mappings and
##  -groups on periodic lists. As these methods need the periodic list code
##  which is implemented in the FR package, this file is read only when FR
##  is available.
##
Revision.perlist_gi :=
  "@(#)$Id$";

#############################################################################
##
#M  \^( <perlist>, <g> ) . . for a periodic list and an rcwa permutation of Z
##
##  The rcwa permutation <g> permutes the entries of the periodic list
##  <perlist>. Periodic lists are implemented in the FR package, which
##  therefore needs to be loaded in order to use this method.
##
InstallMethod( \^,
               "for a periodic list and an rcwa permutation of Z (RCWA)",
               ReturnTrue, [ IsPeriodicList, IsRcwaMappingOfZ ], 0,

  function ( perlist, g )

    local  preperiod, period,
           preperiod_bound, preperiod_img, period_bound, period_img,
           perlist_img, inv;

    preperiod := PrePeriod(perlist);
    period    := Period(perlist);

    if not IsBijective(g) then TryNextMethod(); fi;

    if not IsSignPreserving(g) then
      Error("\^ for a periodic list <l> and an rcwa permutation <g>: \n",
            "<g> must fix the nonnegative integers setwise, as <l> \n",
            "does not have entries at negative positions.");
      TryNextMethod();
    fi;

    inv := Inverse(g);
    period_bound := Mod(g) * Mult(g) * Div(g) * Length(period);
    if not IsEmpty(preperiod) then
      preperiod_bound := Maximum([0..Length(preperiod)-1]^g)+1;
      preperiod_bound := period_bound
                       * (Int((preperiod_bound-1)/period_bound)+1);
    else preperiod_bound := 0; fi;
    preperiod_img := List([0..preperiod_bound-1],n->perlist[n^inv+1]);
    period_img := List([preperiod_bound..preperiod_bound+period_bound-1],
                       n->perlist[n^inv+1]);

    perlist_img := PeriodicList(preperiod_img,period_img);
    CompressPeriodicList(perlist_img);
    return perlist_img;
  end );

#############################################################################
##
#M  \^( <perlist>, <f> ) for a periodic list and a non-bijective rcwa mapping
##
##  The n-th entry of the returned list is the sum of the n^(f^-1)-th entries
##  of <perlist>, where n^(f^-1) denotes the preimage of n under <f>.
##  Periodic lists are implemented in the FR package, which therefore needs
##  to be loaded in order to use this method.
##
InstallMethod( \^,
               "for a periodic list and an rcwa mapping of Z (RCWA)",
               ReturnTrue, [ IsPeriodicList, IsRcwaMappingOfZ ], 0,

  function ( perlist, f )

    local  preperiod, period,
           preperiod_bound, preperiod_img, period_bound, period_img,
           perlist_img, m, r, i;

    preperiod := PrePeriod(perlist);
    period    := Period(perlist);

    if IsBijective(f) or Multiplier(f) = 0 then TryNextMethod(); fi;

    if not IsSignPreserving(f) then
      Error("\^ for a periodic list <l> and an rcwa mapping <f>: \n",
            "<f> must fix the nonnegative integers setwise, as <l> \n",
            "does not have entries at negative positions.");
      TryNextMethod();
    fi;

    period_bound := Mod(f) * Mult(f) * Div(f) * Length(period);
    if not IsEmpty(preperiod) then
      preperiod_bound := Maximum([0..Length(preperiod)-1]^f)+1;
      preperiod_bound := period_bound
                       * (Int((preperiod_bound-1)/period_bound)+1);
    else preperiod_bound := 0; fi;
    preperiod_img := List([0..preperiod_bound-1],
                          n->Sum(perlist{PreImagesElm(f,n)+1}));
    period_img := List([preperiod_bound..preperiod_bound+period_bound-1],
                       n->Sum(perlist{PreImagesElm(f,n)+1}));

    perlist_img := PeriodicList(preperiod_img,period_img);
    CompressPeriodicList(perlist_img);
    return perlist_img;
  end );

#############################################################################
##
#E  perlist.gi . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here