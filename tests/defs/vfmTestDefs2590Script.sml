Theory vfmTestDefs2590[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-2_340282366920938463463374607431768211456_28000_80.json";
val defs = mapi (define_test "2590") tests;
