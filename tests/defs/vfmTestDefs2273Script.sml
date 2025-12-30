Theory vfmTestDefs2273[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcodecall_010_SuicideMiddle2.json";
val defs = mapi (define_test "2273") tests;
