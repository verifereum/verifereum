Theory vfmTestDefs1610[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatacopy_initial/returndatacopy_initial.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatacopy_initial/returndatacopy_initial.json");
val defs = mapi (define_test "1610") tests;
