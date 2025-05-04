open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs045";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip5656_mcopy/mcopy_memory_expansion/mcopy_memory_expansion.json";
val defs = mapi (define_state_test "045") tests;
val () = export_theory_no_docs ();
