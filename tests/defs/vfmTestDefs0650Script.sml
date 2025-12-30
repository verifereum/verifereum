Theory vfmTestDefs0650[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createInitFail_OOGduringInit.json";
val defs = mapi (define_test "0650") tests;
