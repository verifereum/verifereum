Theory vfmTestDefs1983[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_Xto0toXto0.json";
val defs = mapi (define_test "1983") tests;
