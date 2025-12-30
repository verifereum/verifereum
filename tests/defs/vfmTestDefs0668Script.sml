Theory vfmTestDefs0668[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcallcode_01_SuicideEnd.json";
val defs = mapi (define_test "0668") tests;
