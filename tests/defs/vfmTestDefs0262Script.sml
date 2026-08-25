Theory vfmTestDefs0262[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip2935_historical_block_hashes_from_state/test_block_hashes_history.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip2935_historical_block_hashes_from_state/test_block_hashes_history.json");
val defs = mapi (define_test "0262") tests;
