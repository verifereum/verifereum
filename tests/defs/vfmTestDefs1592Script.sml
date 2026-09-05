Theory vfmTestDefs1592[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stReturnDataTest/create_callprecompile_returndatasize/create_callprecompile_returndatasize.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stReturnDataTest/create_callprecompile_returndatasize/create_callprecompile_returndatasize.json");
val defs = mapi (define_test "1592") tests;
