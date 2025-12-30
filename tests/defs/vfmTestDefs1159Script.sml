Theory vfmTestDefs1159[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/log1_dejavu.json";
val defs = mapi (define_test "1159") tests;
