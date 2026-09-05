Theory vfmTestDefs2323[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip2935_historical_block_hashes_from_state/block_hashes/block_hashes_history.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip2935_historical_block_hashes_from_state/block_hashes/block_hashes_history.json");
val defs = mapi (define_test "2323") tests;
