Theory vfmTestDefs0962[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryTest/stack_limit_push32_1024/stack_limit_push32_1024.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryTest/stack_limit_push32_1024/stack_limit_push32_1024.json");
val defs = mapi (define_test "0962") tests;
