Theory vfmTestDefs0128[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_call_large_offset_mstore.json";
val defs = mapi (define_test "0128") tests;
