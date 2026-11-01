Theory vfmTestDefs0243[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip7702/bal_7702_invalid_authority_has_code_authorization.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip7702/bal_7702_invalid_authority_has_code_authorization.json");
val defs = mapi (define_test "0243") tests;
