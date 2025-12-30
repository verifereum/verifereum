Theory vfmTestDefs1968[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/stateRevert.json";
val defs = mapi (define_test "1968") tests;
