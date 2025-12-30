Theory vfmTestDefs2135[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallEcrecoverH_prefixed0.json";
val defs = mapi (define_test "2135") tests;
