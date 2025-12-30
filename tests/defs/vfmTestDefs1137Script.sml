Theory vfmTestDefs1137[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/POP_Bounds.json";
val defs = mapi (define_test "1137") tests;
