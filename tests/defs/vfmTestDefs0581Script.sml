Theory vfmTestDefs0581[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcode_checkPC.json";
val defs = mapi (define_test "0581") tests;
