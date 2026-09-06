Theory vfmTestDefs1602[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatacopy_after_successful_staticcall/returndatacopy_after_successful_staticcall.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stReturnDataTest/returndatacopy_after_successful_staticcall/returndatacopy_after_successful_staticcall.json");
val defs = mapi (define_test "1602") tests;
