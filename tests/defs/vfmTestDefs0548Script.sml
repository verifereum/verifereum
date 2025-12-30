Theory vfmTestDefs0548[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcall_000_SuicideMiddle.json";
val defs = mapi (define_test "0548") tests;
