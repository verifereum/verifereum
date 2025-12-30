Theory vfmTestDefs1997[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSelfBalance/selfBalanceCallTypes.json";
val defs = mapi (define_test "1997") tests;
