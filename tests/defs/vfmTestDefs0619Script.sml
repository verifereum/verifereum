Theory vfmTestDefs0619[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/CallLoseGasOOG.json";
val defs = mapi (define_test "0619") tests;
