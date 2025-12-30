Theory vfmTestDefs1193[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem64kb.json";
val defs = mapi (define_test "1193") tests;
