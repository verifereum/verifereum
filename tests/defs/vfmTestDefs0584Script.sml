Theory vfmTestDefs0584[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecall_10_SuicideEnd.json";
val defs = mapi (define_test "0584") tests;
