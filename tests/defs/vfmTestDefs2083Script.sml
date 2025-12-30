Theory vfmTestDefs2083[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStackTests/underflowTest.json";
val defs = mapi (define_test "2083") tests;
