Theory vfmTestDefs2000[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSelfBalance/selfBalanceUpdate.json";
val defs = mapi (define_test "2000") tests;
