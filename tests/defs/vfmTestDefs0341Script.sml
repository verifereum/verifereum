Theory vfmTestDefs0341[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stArgsZeroOneBalance/slt_non_const/slt_non_const.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stArgsZeroOneBalance/slt_non_const/slt_non_const.json");
val defs = mapi (define_test "0341") tests;
