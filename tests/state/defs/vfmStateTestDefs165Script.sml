open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs165";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip5656_mcopy/mcopy_contexts/no_memory_corruption_on_upper_call_stack_levels.json";
val defs = mapi (define_state_test "165") tests;
val () = export_theory_no_docs ();
