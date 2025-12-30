Theory vfmTestDefs1971[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstoreGas.json";
val defs = mapi (define_test "1971") tests;
