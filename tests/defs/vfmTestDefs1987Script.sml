Theory vfmTestDefs1987[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_XtoXtoX.json";
val defs = mapi (define_test "1987") tests;
