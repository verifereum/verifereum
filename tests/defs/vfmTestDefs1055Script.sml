Theory vfmTestDefs1055[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/TransactionCreateStopInInitcode.json";
val defs = mapi (define_test "1055") tests;
