Theory vfmTestDefs0618[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/Call1024PreCalls.json";
val defs = mapi (define_test "0618") tests;
