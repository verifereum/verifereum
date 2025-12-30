Theory vfmTestDefs0542[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcall_00_SuicideEnd.json";
val defs = mapi (define_test "0542") tests;
