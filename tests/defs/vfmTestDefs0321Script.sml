Theory vfmTestDefs0321[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stArgsZeroOneBalance/jumpi_non_const/jumpi_non_const.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stArgsZeroOneBalance/jumpi_non_const/jumpi_non_const.json");
val defs = mapi (define_test "0321") tests;
