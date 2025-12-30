Theory vfmTestDefs0142[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_swap.json";
val defs = mapi (define_test "0142") tests;
