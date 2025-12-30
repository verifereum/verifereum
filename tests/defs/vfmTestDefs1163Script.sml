Theory vfmTestDefs1163[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem0b_singleByte.json";
val defs = mapi (define_test "1163") tests;
