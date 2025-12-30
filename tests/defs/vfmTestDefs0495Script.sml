Theory vfmTestDefs0495[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/extcodecopyNonConst.json";
val defs = mapi (define_test "0495") tests;
