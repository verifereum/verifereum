Theory vfmTestDefs0393[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_multiple_withdrawals_same_address.json";
val defs = mapi (define_test "0393") tests;
