Theory vfmTestDefs1203[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/memCopySelf.json";
val defs = mapi (define_test "1203") tests;
