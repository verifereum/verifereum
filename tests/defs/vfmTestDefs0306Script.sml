Theory vfmTestDefs0306[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_call_to_precompile_in_pointer_context.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_call_to_precompile_in_pointer_context.json");
val defs = mapi (define_test "0306") tests;
