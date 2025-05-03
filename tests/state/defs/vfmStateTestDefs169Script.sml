open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs169";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip5656_mcopy/mcopy/valid_mcopy_operations.json";
val defs = mapi (define_state_test "169") tests;
val () = export_theory_no_docs ();
