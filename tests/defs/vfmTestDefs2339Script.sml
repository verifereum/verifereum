Theory vfmTestDefs2339[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stReturnDataTest/subcall_return_more_then_expected/subcall_return_more_then_expected.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stReturnDataTest/subcall_return_more_then_expected/subcall_return_more_then_expected.json");
val defs = mapi (define_test "2339") tests;
