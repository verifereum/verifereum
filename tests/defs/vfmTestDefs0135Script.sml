Theory vfmTestDefs0135[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_double_kill.json";
val defs = mapi (define_test "0135") tests;
