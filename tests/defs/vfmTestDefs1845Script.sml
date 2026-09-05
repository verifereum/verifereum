Theory vfmTestDefs1845[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_to_call_op_code_check/static_call_to_call_op_code_check.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_to_call_op_code_check/static_call_to_call_op_code_check.json");
val defs = mapi (define_test "1845") tests;
