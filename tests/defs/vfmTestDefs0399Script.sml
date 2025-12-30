Theory vfmTestDefs0399[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_withdrawals_root.json";
val defs = mapi (define_test "0399") tests;
