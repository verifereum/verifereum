Theory vfmTestDefs0126[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_all_opcodes.json";
val defs = mapi (define_test "0126") tests;
