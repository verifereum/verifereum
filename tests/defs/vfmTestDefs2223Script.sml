Theory vfmTestDefs2223[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_call_OOG_additionalGasCosts1.json";
val defs = mapi (define_test "2223") tests;
