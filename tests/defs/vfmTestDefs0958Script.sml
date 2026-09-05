Theory vfmTestDefs0958[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryTest/stack_limit_push31_1023/stack_limit_push31_1023.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryTest/stack_limit_push31_1023/stack_limit_push31_1023.json");
val defs = mapi (define_test "0958") tests;
