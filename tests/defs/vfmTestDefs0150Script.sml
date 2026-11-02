Theory vfmTestDefs0150[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists/bal_cross_tx_reverted_storage_reads.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists/bal_cross_tx_reverted_storage_reads.json");
val defs = mapi (define_test "0150") tests;
