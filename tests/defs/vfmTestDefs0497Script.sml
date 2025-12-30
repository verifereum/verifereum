Theory vfmTestDefs0497[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/gtNonConst.json";
val defs = mapi (define_test "0497") tests;
