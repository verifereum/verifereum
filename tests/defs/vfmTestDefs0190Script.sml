Theory vfmTestDefs0190[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_cross_index/bal_pre_execution_call_failure_keeps_read_drops_write.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_cross_index/bal_pre_execution_call_failure_keeps_read_drops_write.json");
val defs = mapi (define_test "0190") tests;
