Theory vfmTestDefs2428[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/createNameRegistratorValueTooHigh.json";
val defs = mapi (define_test "2428") tests;
