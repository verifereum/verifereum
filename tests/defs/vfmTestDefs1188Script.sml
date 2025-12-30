Theory vfmTestDefs1188[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem64kb+33.json";
val defs = mapi (define_test "1188") tests;
