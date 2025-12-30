Theory vfmTestDefs0778[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCodeCopyTest/ExtCodeCopyTestsParis.json";
val defs = mapi (define_test "0778") tests;
