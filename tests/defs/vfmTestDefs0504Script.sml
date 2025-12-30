Theory vfmTestDefs0504[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/log3NonConst.json";
val defs = mapi (define_test "0504") tests;
