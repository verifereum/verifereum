Theory vfmTestDefs1211[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/sha3_dejavu.json";
val defs = mapi (define_test "1211") tests;
