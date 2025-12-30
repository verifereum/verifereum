Theory vfmTestDefs0140[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_stack_overflow.json";
val defs = mapi (define_test "0140") tests;
