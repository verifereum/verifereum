Theory vfmTestDefs2195[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_RETURN_BoundsOOG.json";
val defs = mapi (define_test "2195") tests;
