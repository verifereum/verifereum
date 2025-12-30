Theory vfmTestDefs2415[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/balanceInputAddressTooBig.json";
val defs = mapi (define_test "2415") tests;
