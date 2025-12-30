Theory vfmTestDefs1156[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/codecopy_dejavu.json";
val defs = mapi (define_test "1156") tests;
