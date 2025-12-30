Theory vfmTestDefs1051[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/ReturnTest2.json";
val defs = mapi (define_test "1051") tests;
