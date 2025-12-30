Theory vfmTestDefs2439[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/return1.json";
val defs = mapi (define_test "2439") tests;
