Theory vfmTestDefs0275[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_invalid/bal_invalid_missing_system_contract_entry.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_invalid/bal_invalid_missing_system_contract_entry.json");
val defs = mapi (define_test "0275") tests;
