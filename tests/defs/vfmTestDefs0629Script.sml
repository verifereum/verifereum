Theory vfmTestDefs0629[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callOutput3partialFail.json";
val defs = mapi (define_test "0629") tests;
