Theory vfmTestDefs0392[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_many_withdrawals.json";
val defs = mapi (define_test "0392") tests;
