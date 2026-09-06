Theory vfmTestDefs0319[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stArgsZeroOneBalance/iszero_non_const/iszero_non_const.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stArgsZeroOneBalance/iszero_non_const/iszero_non_const.json");
val defs = mapi (define_test "0319") tests;
