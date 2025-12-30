Theory vfmTestDefs0384[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3855_push0/test_push0_contract_during_call_contexts.json";
val defs = mapi (define_test "0384") tests;
