Theory vfmTestDefs2425[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/createNameRegistratorOOG_MemExpansionOOV.json";
val defs = mapi (define_test "2425") tests;
