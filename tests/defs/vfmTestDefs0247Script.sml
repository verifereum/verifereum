Theory vfmTestDefs0247[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip7702/bal_7702_null_address_delegation_no_code_change.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip7702/bal_7702_null_address_delegation_no_code_change.json");
val defs = mapi (define_test "0247") tests;
