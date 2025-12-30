Theory vfmTestDefs0053[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_call_opcode_types.json";
val defs = mapi (define_test "0053") tests;
