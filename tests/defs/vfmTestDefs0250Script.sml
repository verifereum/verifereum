Theory vfmTestDefs0250[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip7702/bal_selfdestruct_to_7702_delegation.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip7702/bal_selfdestruct_to_7702_delegation.json");
val defs = mapi (define_test "0250") tests;
