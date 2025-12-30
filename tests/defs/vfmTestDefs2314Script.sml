Theory vfmTestDefs2314[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcall_ABCB_RECURSIVE2.json";
val defs = mapi (define_test "2314") tests;
