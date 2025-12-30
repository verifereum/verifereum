Theory vfmTestDefs2625[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-3_340282366920938463463374607431768211456_21000_80.json";
val defs = mapi (define_test "2625") tests;
