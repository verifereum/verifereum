Theory vfmTestDefs0512[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/notNonConst.json";
val defs = mapi (define_test "0512") tests;
