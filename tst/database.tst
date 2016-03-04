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
gap> data := LoadDatabaseOfProductsOf2ClassTranspositions();;
gap> Set(RecNames(data));
[ "CTPairIntersectionType", "CTPairProductType", "CTPairs", 
  "CTPairsIntersectionTypes", "CTPairsProductClassification", 
  "CTPairsProductType", "CTProds12", "CTProds32", "OrdersMatrix" ]
gap> data := LoadDatabaseOfNonbalancedProductsOfClassTranspositions();;
gap> Set(RecNames(data));
[ "PairsOfCTsWhoseProductIsNotBalanced", 
  "TriplesOfCTsWhoseProductHasCoprimeMultiplierAndDivisor" ]
gap> data := LoadDatabaseOfGroupsGeneratedBy3ClassTranspositions(6);;
gap> Set(RecNames(data));
[ "3CTsGroupsWithGivenOrbit", "Id3CTsGroup", "ProbablyFixesDigitSumsModulo", 
  "ProbablyStabilizesDigitSumsModulo", "TriangleTypes", "abc_torsion", 
  "chains", "conjugacyclasses", "cts", "cyclist", "degrees", "eqclsgt1", 
  "equalityclasses", "finiteorbits", "freeproductcandidates", 
  "freeproductlikes", "groups", "grps", "intransitivemodulo", "mods", 
  "orbitgrowthtype", "orbitlengths", "partitionlengths", "permgroupgens", 
  "respectedpartitions", "shortresidueclassorbitlengths", "sizes", 
  "sizespos", "sizesset", "stabilize_digitsum_base2_mod2", 
  "stabilize_digitsum_base2_mod3", "stabilize_digitsum_base3_mod2", 
  "subgroups", "supergroups", "trsstatus", "trsstatuspos", "trsstatusset" ]
gap> data := LoadDatabaseOfGroupsGeneratedBy3ClassTranspositions(9);;
gap> Set(RecNames(data));
[ "cts", "mods", "partlengths", "sizes" ]
gap> data := LoadDatabaseOfGroupsGeneratedBy4ClassTranspositions();;
gap> Set(RecNames(data));
[ "conjugacyclasses4cts", "cts", "grps4_3finite", "grps4_3finite_reps", 
  "grps4_3finitepos", "mods4", "sizes4", "sizes4pos", "sizes4set" ]
gap> data := LoadDatabaseOfCTGraphs();;
gap> Set(RecNames(data));
[ "embeddings4", "embeddings5", "embeddings6" ]
gap> RCWADoThingsToBeDoneAfterTest();
gap> STOP_TEST( "database.tst", 4500000000 );

#############################################################################
##
#E  database.tst . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
