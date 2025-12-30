Theory vfmTestDefs0132[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_calldatasize.json";
val defs = mapi (define_test "0132") tests;
