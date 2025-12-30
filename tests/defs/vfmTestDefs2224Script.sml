Theory vfmTestDefs2224[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_call_OOG_additionalGasCosts2_Paris.json";
val defs = mapi (define_test "2224") tests;
