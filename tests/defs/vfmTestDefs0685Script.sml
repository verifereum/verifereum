Theory vfmTestDefs0685[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecall_10_SuicideEnd.json";
val defs = mapi (define_test "0685") tests;
