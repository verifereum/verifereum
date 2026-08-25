Theory vfmTestDefs1884[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/call_outsize_then_create_successful_then_returndatasize.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stReturnDataTest/call_outsize_then_create_successful_then_returndatasize.json");
val defs = mapi (define_test "1884") tests;
