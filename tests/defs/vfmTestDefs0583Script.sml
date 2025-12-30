Theory vfmTestDefs0583[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecall_10_OOGE.json";
val defs = mapi (define_test "0583") tests;
