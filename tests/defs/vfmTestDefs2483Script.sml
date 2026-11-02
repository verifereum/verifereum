Theory vfmTestDefs2483[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStackTests/stack_overflow_m1/stack_overflow_m1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStackTests/stack_overflow_m1/stack_overflow_m1.json");
val defs = mapi (define_test "2483") tests;
