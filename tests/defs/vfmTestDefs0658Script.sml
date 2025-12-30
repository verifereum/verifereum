Theory vfmTestDefs0658[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createNameRegistratorendowmentTooHigh.json";
val defs = mapi (define_test "0658") tests;
