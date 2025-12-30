Theory vfmTestDefs0127[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_call_large_args_offset_size_zero.json";
val defs = mapi (define_test "0127") tests;
