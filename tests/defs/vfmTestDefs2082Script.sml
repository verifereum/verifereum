Theory vfmTestDefs2082[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStackTests/stacksanitySWAP.json";
val defs = mapi (define_test "2082") tests;
