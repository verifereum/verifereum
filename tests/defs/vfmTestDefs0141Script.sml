Theory vfmTestDefs0141[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_stack_underflow.json";
val defs = mapi (define_test "0141") tests;
