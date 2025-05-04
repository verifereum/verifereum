open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs044";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip5656_mcopy/mcopy_memory_expansion/mcopy_huge_memory_expansion.json";
val defs = mapi (define_state_test "044") tests;
val () = export_theory_no_docs ();
