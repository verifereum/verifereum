Theory vfmTestDefs1208[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mstore_dejavu.json";
val defs = mapi (define_test "1208") tests;
