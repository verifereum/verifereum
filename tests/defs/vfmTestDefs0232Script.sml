Theory vfmTestDefs0232[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip7251/bal_system_dequeue_consolidations_eip7251.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip7251/bal_system_dequeue_consolidations_eip7251.json");
val defs = mapi (define_test "0232") tests;
