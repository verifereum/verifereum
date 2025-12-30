Theory vfmTestDefs0294[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/test_transaction_validity_type_3.json";
val defs = mapi (define_test "0294") tests;
