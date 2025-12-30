Theory vfmTestDefs0616[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/Call1024BalanceTooLow.json";
val defs = mapi (define_test "0616") tests;
