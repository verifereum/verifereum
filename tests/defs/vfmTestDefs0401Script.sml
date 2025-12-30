Theory vfmTestDefs0401[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_zero_amount.json";
val defs = mapi (define_test "0401") tests;
