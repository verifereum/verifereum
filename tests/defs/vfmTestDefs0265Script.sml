Theory vfmTestDefs0265[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip2935_historical_block_hashes_from_state/test_invalid_history_contract_calls.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip2935_historical_block_hashes_from_state/test_invalid_history_contract_calls.json");
val defs = mapi (define_test "0265") tests;
