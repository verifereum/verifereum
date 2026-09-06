Theory vfmTestDefs1654[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRevertTest/revert_precompiled_touch_storage_paris/revert_precompiled_touch_storage_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRevertTest/revert_precompiled_touch_storage_paris/revert_precompiled_touch_storage_paris.json");
val defs = mapi (define_test "1654") tests;
