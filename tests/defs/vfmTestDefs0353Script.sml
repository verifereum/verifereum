Theory vfmTestDefs0353[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_max_depth_call_stack.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_set_code_max_depth_call_stack.json");
val defs = mapi (define_test "0353") tests;
