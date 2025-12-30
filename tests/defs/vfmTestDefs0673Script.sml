Theory vfmTestDefs0673[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcallcodecall_010_SuicideEnd.json";
val defs = mapi (define_test "0673") tests;
