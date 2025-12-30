Theory vfmTestDefs0601[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecallcode_11_SuicideEnd.json";
val defs = mapi (define_test "0601") tests;
