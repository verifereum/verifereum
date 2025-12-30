Theory vfmTestDefs1991[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_XtoYtoX.json";
val defs = mapi (define_test "1991") tests;
