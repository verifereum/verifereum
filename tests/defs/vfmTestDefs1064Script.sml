Theory vfmTestDefs1064[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log1_Caller.json";
val defs = mapi (define_test "1064") tests;
