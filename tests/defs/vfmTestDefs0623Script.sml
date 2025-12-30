Theory vfmTestDefs0623[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/CallcodeLoseGasOOG.json";
val defs = mapi (define_test "0623") tests;
