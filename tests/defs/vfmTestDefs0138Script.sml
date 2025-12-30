Theory vfmTestDefs0138[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_genesis_hash_available.json";
val defs = mapi (define_test "0138") tests;
