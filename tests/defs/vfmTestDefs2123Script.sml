Theory vfmTestDefs2123[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallEcrecover0_0input.json";
val defs = mapi (define_test "2123") tests;
