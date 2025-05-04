open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs040";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip5656_mcopy/mcopy/mcopy_on_empty_memory.json";
val defs = mapi (define_state_test "040") tests;
val () = export_theory_no_docs ();
