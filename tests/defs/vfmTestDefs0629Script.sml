Theory vfmTestDefs0629[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/returndatacopy_0_0_following_successful_create/returndatacopy_0_0_following_successful_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/returndatacopy_0_0_following_successful_create/returndatacopy_0_0_following_successful_create.json");
val defs = mapi (define_test "0629") tests;
