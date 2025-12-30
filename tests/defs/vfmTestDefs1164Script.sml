Theory vfmTestDefs1164[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem31b_singleByte.json";
val defs = mapi (define_test "1164") tests;
