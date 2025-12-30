Theory vfmTestDefs0617[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/Call1024OOG.json";
val defs = mapi (define_test "0617") tests;
