Theory vfmTestDefs2353[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_log0_emptyMem.json";
val defs = mapi (define_test "2353") tests;
