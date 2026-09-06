Theory vfmTestDefs0596[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/call_then_create2_successful_then_returndatasize/call_then_create2_successful_then_returndatasize.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/call_then_create2_successful_then_returndatasize/call_then_create2_successful_then_returndatasize.json");
val defs = mapi (define_test "0596") tests;
