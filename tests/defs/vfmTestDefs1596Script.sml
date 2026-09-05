Theory vfmTestDefs1596[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatacopy_after_failing_create/returndatacopy_after_failing_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatacopy_after_failing_create/returndatacopy_after_failing_create.json");
val defs = mapi (define_test "1596") tests;
