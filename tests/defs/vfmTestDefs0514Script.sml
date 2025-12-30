Theory vfmTestDefs0514[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/returnNonConst.json";
val defs = mapi (define_test "0514") tests;
