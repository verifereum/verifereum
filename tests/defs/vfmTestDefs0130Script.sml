Theory vfmTestDefs0130[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_calldatacopy.json";
val defs = mapi (define_test "0130") tests;
