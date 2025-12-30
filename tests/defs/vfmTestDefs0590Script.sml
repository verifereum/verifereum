Theory vfmTestDefs0590[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecallcall_100_SuicideMiddle.json";
val defs = mapi (define_test "0590") tests;
