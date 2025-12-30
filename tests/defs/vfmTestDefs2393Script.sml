Theory vfmTestDefs2393[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallRecursiveBomb2.json";
val defs = mapi (define_test "2393") tests;
