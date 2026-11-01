Theory vfmTestDefs0295[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_opcodes/bal_call_revert_insufficient_funds.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_opcodes/bal_call_revert_insufficient_funds.json");
val defs = mapi (define_test "0295") tests;
