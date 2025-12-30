Theory vfmTestDefs2104[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call1024PreCalls.json";
val defs = mapi (define_test "2104") tests;
