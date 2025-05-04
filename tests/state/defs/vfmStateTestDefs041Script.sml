open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs041";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip5656_mcopy/mcopy/valid_mcopy_operations.json";
val defs = mapi (define_state_test "041") tests;
val () = export_theory_no_docs ();
