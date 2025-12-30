Theory vfmTestDefs2079[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStackTests/stackOverflowM1PUSH.json";
val defs = mapi (define_test "2079") tests;
