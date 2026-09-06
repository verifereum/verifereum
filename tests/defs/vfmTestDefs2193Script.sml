Theory vfmTestDefs2193[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stZeroCallsTest/zero_value_call_to_empty_paris/zero_value_call_to_empty_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stZeroCallsTest/zero_value_call_to_empty_paris/zero_value_call_to_empty_paris.json");
val defs = mapi (define_test "2193") tests;
