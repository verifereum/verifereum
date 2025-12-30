Theory vfmTestDefs0691[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcall_100_SuicideMiddle.json";
val defs = mapi (define_test "0691") tests;
