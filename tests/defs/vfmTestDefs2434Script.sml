Theory vfmTestDefs2434[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/doubleSelfdestructTest.json";
val defs = mapi (define_test "2434") tests;
