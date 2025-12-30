Theory vfmTestDefs2416[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/callValue.json";
val defs = mapi (define_test "2416") tests;
