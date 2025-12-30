Theory vfmTestDefs0519[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/sloadNonConst.json";
val defs = mapi (define_test "0519") tests;
