Theory vfmTestDefs1668[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRevertTest/touch_to_empty_account_revert_paris/touch_to_empty_account_revert_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRevertTest/touch_to_empty_account_revert_paris/touch_to_empty_account_revert_paris.json");
val defs = mapi (define_test "1668") tests;
