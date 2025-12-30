Theory vfmTestDefs1102[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/logInOOG_Call.json";
val defs = mapi (define_test "1102") tests;
