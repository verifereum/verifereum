Theory vfmTestDefs1973[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_0to0to0.json";
val defs = mapi (define_test "1973") tests;
