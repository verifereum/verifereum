Theory vfmTestDefs2449[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/testRandomTest.json";
val defs = mapi (define_test "2449") tests;
