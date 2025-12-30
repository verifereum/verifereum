Theory vfmTestDefs0133[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_constant_gas.json";
val defs = mapi (define_test "0133") tests;
