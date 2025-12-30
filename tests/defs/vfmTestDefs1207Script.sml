Theory vfmTestDefs1207[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mload_dejavu.json";
val defs = mapi (define_test "1207") tests;
