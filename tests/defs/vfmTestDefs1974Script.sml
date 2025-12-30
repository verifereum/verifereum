Theory vfmTestDefs1974[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_0to0toX.json";
val defs = mapi (define_test "1974") tests;
