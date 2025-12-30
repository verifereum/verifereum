Theory vfmTestDefs2424[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/createNameRegistrator.json";
val defs = mapi (define_test "2424") tests;
