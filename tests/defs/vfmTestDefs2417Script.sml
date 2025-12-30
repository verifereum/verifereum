Theory vfmTestDefs2417[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/callcodeTo0.json";
val defs = mapi (define_test "2417") tests;
