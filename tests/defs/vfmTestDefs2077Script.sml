Theory vfmTestDefs2077[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/double_selfdestruct_test/double_selfdestruct_test.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/double_selfdestruct_test/double_selfdestruct_test.json");
val defs = mapi (define_test "2077") tests;
