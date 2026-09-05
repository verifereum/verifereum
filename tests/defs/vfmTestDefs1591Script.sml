Theory vfmTestDefs1591[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stReturnDataTest/clear_return_buffer/clear_return_buffer.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stReturnDataTest/clear_return_buffer/clear_return_buffer.json");
val defs = mapi (define_test "1591") tests;
