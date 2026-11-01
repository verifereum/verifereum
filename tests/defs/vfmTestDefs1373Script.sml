Theory vfmTestDefs1373[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCreate2/returndatacopy_following_revert_in_create/returndatacopy_following_revert_in_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCreate2/returndatacopy_following_revert_in_create/returndatacopy_following_revert_in_create.json");
val defs = mapi (define_test "1373") tests;
