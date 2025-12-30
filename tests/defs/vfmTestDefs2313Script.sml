Theory vfmTestDefs2313[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcall_ABCB_RECURSIVE.json";
val defs = mapi (define_test "2313") tests;
