Theory vfmTestDefs0651[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createInitFail_OOGduringInit2.json";
val defs = mapi (define_test "0651") tests;
