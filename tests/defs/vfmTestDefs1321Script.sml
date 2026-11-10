Theory vfmTestDefs1321[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCallCreateCallCodeTest/create_init_fail_stack_size_larger_than1024/create_init_fail_stack_size_larger_than1024.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCallCreateCallCodeTest/create_init_fail_stack_size_larger_than1024/create_init_fail_stack_size_larger_than1024.json");
val defs = mapi (define_test "1321") tests;
