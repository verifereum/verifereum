Theory vfmTestDefs0187[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_cross_index/bal_intra_tx_round_trip_after_prior_tx_write.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_cross_index/bal_intra_tx_round_trip_after_prior_tx_write.json");
val defs = mapi (define_test "0187") tests;
