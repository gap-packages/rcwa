#############################################################################
##
#W  database.tst               GAP4 Package `RCWA'                Stefan Kohl
##
##  This file contains tests whether RCWA's databases of rcwa groups and
##  rcwa mappings can be loaded correctly.
##
#############################################################################

gap> START_TEST( "database.tst" );
gap> RCWADoThingsToBeDoneBeforeTest();
gap> LoadDatabaseOfProductsOf2ClassTranspositions();
"CTProducts"
gap> Set(RecNames(CTProducts));
[ "CTPairIntersectionType", "CTPairProductType", "CTPairs", 
  "CTPairsIntersectionTypes", "CTPairsProductClassification", 
  "CTPairsProductType", "CTProds12", "CTProds32", "OrdersMatrix" ]
gap> LoadDatabaseOfNonbalancedProductsOfClassTranspositions();
"CTProductsNB"
gap> Set(RecNames(CTProductsNB));
[ "PairsOfCTsWhoseProductIsNotBalanced", 
  "TriplesOfCTsWhoseProductHasCoprimeMultiplierAndDivisor" ]
gap> LoadDatabaseOfGroupsGeneratedBy3ClassTranspositions(6);
"3CTsGroups6"
gap> Set(RecNames(3CTsGroups6));
[ "3CTsGroupsWithGivenOrbit", "Id3CTsGroup", "ProbablyFixesDigitSumsModulo", 
  "ProbablyStabilizesDigitSumsModulo", "TriangleTypes", "abc_torsion", 
  "chains", "conjugacyclasses", "cts", "cyclist", "degrees", 
  "equalityclasses", "finiteorbits", "freeproductcandidates", 
  "freeproductlikes", "groups", "grps", "intransitivemodulo", "mods", 
  "orbitgrowthtype", "orbitlengths", "partitionlengths", "permgroupgens", 
  "respectedpartitions", "samegroups", "shortresidueclassorbitlengths", 
  "sizes", "sizespos", "sizesset", "stabilize_digitsum_base2_mod2", 
  "stabilize_digitsum_base2_mod3", "stabilize_digitsum_base3_mod2", 
  "subgroups", "supergroups", "trsstatus", "trsstatuspos", "trsstatusset" ]
gap> LoadDatabaseOfGroupsGeneratedBy3ClassTranspositions(9);
"3CTsGroups9"
gap> Set(RecNames(3CTsGroups9));
[ "All3CTs9Groups", "All3CTs9Indices", "cts", "mods", "partlengths", "sizes" ]
gap> LoadDatabaseOfGroupsGeneratedBy4ClassTranspositions();
"4CTsGroups6"
gap> Set(RecNames(4CTsGroups6));
[ "conjugacyclasses4cts", "cts", "grps4_3finite", "grps4_3finite_reps", 
  "grps4_3finitepos", "mods4", "sizes4", "sizes4pos", "sizes4set" ]
gap> LoadDatabaseOfCTGraphs();
"CTGraphs"
gap> Set(RecNames(CTGraphs));
[ "embeddings4", "embeddings5", "embeddings6" ]
gap> RCWADoThingsToBeDoneAfterTest();
gap> STOP_TEST( "database.tst", 4500000000 );

#############################################################################
##
#E  database.tst . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
