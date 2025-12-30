Theory vfmTestDefs0266[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2935_historical_block_hashes_from_state/test_invalid_history_contract_calls_input_size.json";
val defs = mapi (define_test "0266") tests;
