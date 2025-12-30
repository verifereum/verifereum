Theory vfmTestDefs2413[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/PostToReturn1.json";
val defs = mapi (define_test "2413") tests;
