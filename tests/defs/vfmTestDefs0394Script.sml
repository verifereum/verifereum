Theory vfmTestDefs0394[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_newly_created_contract.json";
val defs = mapi (define_test "0394") tests;
