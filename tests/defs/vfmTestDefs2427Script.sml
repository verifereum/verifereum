Theory vfmTestDefs2427[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/createNameRegistratorOutOfMemoryBonds1.json";
val defs = mapi (define_test "2427") tests;
