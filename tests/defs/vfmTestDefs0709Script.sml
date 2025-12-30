Theory vfmTestDefs0709[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_ABCB_RECURSIVE.json";
val defs = mapi (define_test "0709") tests;
