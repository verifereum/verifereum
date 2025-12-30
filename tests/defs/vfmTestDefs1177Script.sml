Theory vfmTestDefs1177[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem32kb_singleByte+32.json";
val defs = mapi (define_test "1177") tests;
