Theory vfmTestDefs2271[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcodecall_010_SuicideEnd2.json";
val defs = mapi (define_test "2271") tests;
