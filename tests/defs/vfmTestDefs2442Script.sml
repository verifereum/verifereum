Theory vfmTestDefs2442[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/suicideCaller.json";
val defs = mapi (define_test "2442") tests;
