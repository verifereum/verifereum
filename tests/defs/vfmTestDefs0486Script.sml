Theory vfmTestDefs0486[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/callcodeNonConst.json";
val defs = mapi (define_test "0486") tests;
