Theory vfmTestDefs1157[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/codecopy_dejavu2.json";
val defs = mapi (define_test "1157") tests;
