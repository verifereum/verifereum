Theory vfmTestDefs0263[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip2935_historical_block_hashes_from_state/test_block_hashes_history_at_transition.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip2935_historical_block_hashes_from_state/test_block_hashes_history_at_transition.json");
val defs = mapi (define_test "0263") tests;
