Theory vfmTestDefs0621[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/Callcode1024BalanceTooLow.json";
val defs = mapi (define_test "0621") tests;
