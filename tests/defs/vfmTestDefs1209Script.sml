Theory vfmTestDefs1209[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mstroe8_dejavu.json";
val defs = mapi (define_test "1209") tests;
