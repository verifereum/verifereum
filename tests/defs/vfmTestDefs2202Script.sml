Theory vfmTestDefs2202[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_ZeroValue_CALL_OOGRevert.json";
val defs = mapi (define_test "2202") tests;
