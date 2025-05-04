open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs043";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip5656_mcopy/mcopy_contexts/no_memory_corruption_on_upper_create_stack_levels.json";
val defs = mapi (define_state_test "043") tests;
val () = export_theory_no_docs ();
