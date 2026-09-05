Theory vfmTestDefs1588[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stReturnDataTest/call_outsize_then_create_successful_then_returndatasize/call_outsize_then_create_successful_then_returndatasize.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stReturnDataTest/call_outsize_then_create_successful_then_returndatasize/call_outsize_then_create_successful_then_returndatasize.json");
val defs = mapi (define_test "1588") tests;
