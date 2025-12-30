Theory vfmTestDefs0134[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_cover_revert.json";
val defs = mapi (define_test "0134") tests;
