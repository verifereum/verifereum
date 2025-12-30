Theory vfmTestDefs0655[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createNameRegistratorPerTxs.json";
val defs = mapi (define_test "0655") tests;
