Theory vfmTestDefs0400[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_withdrawing_to_precompiles.json";
val defs = mapi (define_test "0400") tests;
