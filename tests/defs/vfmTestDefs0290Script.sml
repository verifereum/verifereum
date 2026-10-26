Theory vfmTestDefs0290[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_opcodes/bal_account_touch_system_address.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_opcodes/bal_account_touch_system_address.json");
val defs = mapi (define_test "0290") tests;
