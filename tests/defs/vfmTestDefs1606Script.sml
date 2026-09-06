Theory vfmTestDefs1606[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatacopy_following_revert/returndatacopy_following_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatacopy_following_revert/returndatacopy_following_revert.json");
val defs = mapi (define_test "1606") tests;
