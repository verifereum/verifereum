Theory vfmTestDefs2207[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callCreate2.json";
val defs = mapi (define_test "2207") tests;
