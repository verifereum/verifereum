Theory vfmTestDefs0196[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_cross_index/bal_withdrawals_and_dequeues_net_balance_at_last_index.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_cross_index/bal_withdrawals_and_dequeues_net_balance_at_last_index.json");
val defs = mapi (define_test "0196") tests;
