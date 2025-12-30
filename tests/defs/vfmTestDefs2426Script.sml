Theory vfmTestDefs2426[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/createNameRegistratorOutOfMemoryBonds0.json";
val defs = mapi (define_test "2426") tests;
