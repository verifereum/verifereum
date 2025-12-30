Theory vfmTestDefs0493[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/eqNonConst.json";
val defs = mapi (define_test "0493") tests;
