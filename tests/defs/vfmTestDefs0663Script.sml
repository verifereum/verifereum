Theory vfmTestDefs0663[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcallcallcode_001_SuicideEnd.json";
val defs = mapi (define_test "0663") tests;
