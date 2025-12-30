Theory vfmTestDefs0482[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/andNonConst.json";
val defs = mapi (define_test "0482") tests;
