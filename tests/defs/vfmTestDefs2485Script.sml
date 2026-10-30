Theory vfmTestDefs2485[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStackTests/stack_overflow_m1_push/stack_overflow_m1_push.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStackTests/stack_overflow_m1_push/stack_overflow_m1_push.json");
val defs = mapi (define_test "2485") tests;
