Theory vfmTestDefs0462[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/create_init_fail_stack_underflow/create_init_fail_stack_underflow.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/create_init_fail_stack_underflow/create_init_fail_stack_underflow.json");
val defs = mapi (define_test "0462") tests;
