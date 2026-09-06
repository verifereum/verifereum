Theory vfmTestDefs1639[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRevertTest/revert_on_empty_stack/revert_on_empty_stack.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRevertTest/revert_on_empty_stack/revert_on_empty_stack.json");
val defs = mapi (define_test "1639") tests;
