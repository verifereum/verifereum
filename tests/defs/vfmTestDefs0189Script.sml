Theory vfmTestDefs0189[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_cross_index/bal_post_execution_calls_net_storage_at_last_index.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_cross_index/bal_post_execution_calls_net_storage_at_last_index.json");
val defs = mapi (define_test "0189") tests;
