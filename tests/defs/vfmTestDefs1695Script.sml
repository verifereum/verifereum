Theory vfmTestDefs1695[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stMemoryTest/stack_limit_push31_1025/stack_limit_push31_1025.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stMemoryTest/stack_limit_push31_1025/stack_limit_push31_1025.json");
val defs = mapi (define_test "1695") tests;
