Theory vfmTestDefs2151[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallRecursiveBomb0_OOG_atMaxCallDepth.json";
val defs = mapi (define_test "2151") tests;
