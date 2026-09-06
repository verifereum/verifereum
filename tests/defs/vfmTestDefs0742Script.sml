Theory vfmTestDefs0742[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP158Specific/call_to_empty_then_call_error_paris/call_to_empty_then_call_error_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP158Specific/call_to_empty_then_call_error_paris/call_to_empty_then_call_error_paris.json");
val defs = mapi (define_test "0742") tests;
