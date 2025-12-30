Theory vfmTestDefs2019[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shiftSignedCombinations.json";
val defs = mapi (define_test "2019") tests;
