Theory vfmTestDefs1262[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stArgsZeroOneBalance/sub_non_const/sub_non_const.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stArgsZeroOneBalance/sub_non_const/sub_non_const.json");
val defs = mapi (define_test "1262") tests;
