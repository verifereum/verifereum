Theory vfmTestDefs0017[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_reentrant_call.json";
val defs = mapi (define_test "0017") tests;
