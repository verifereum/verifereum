Theory vfmTestDefs1989[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_XtoY.json";
val defs = mapi (define_test "1989") tests;
