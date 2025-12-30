Theory vfmTestDefs0643[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createFailBalanceTooLow.json";
val defs = mapi (define_test "0643") tests;
