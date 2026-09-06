Theory vfmTestDefs1773[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStackTests/stack_overflow_swap/stack_overflow_swap.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStackTests/stack_overflow_swap/stack_overflow_swap.json");
val defs = mapi (define_test "1773") tests;
