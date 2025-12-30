Theory vfmTestDefs0525[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/xorNonConst.json";
val defs = mapi (define_test "0525") tests;
