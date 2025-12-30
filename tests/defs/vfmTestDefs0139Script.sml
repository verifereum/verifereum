Theory vfmTestDefs0139[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_push.json";
val defs = mapi (define_test "0139") tests;
