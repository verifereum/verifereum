Theory vfmTestDefs0518[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/signextNonConst.json";
val defs = mapi (define_test "0518") tests;
