Theory vfmTestDefs0513[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/orNonConst.json";
val defs = mapi (define_test "0513") tests;
