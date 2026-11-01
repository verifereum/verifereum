Theory vfmTestDefs0209[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip4788/bal_4788_selfdestruct_to_beacon_root.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip4788/bal_4788_selfdestruct_to_beacon_root.json");
val defs = mapi (define_test "0209") tests;
