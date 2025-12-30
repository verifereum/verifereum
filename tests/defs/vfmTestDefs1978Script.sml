Theory vfmTestDefs1978[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_0toXtoX.json";
val defs = mapi (define_test "1978") tests;
