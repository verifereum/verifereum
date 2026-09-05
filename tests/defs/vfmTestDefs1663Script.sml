Theory vfmTestDefs1663[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRevertTest/revert_sub_call_storage_oog/revert_sub_call_storage_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRevertTest/revert_sub_call_storage_oog/revert_sub_call_storage_oog.json");
val defs = mapi (define_test "1663") tests;
