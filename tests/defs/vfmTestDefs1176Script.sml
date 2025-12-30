Theory vfmTestDefs1176[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem32kb_singleByte+31.json";
val defs = mapi (define_test "1176") tests;
