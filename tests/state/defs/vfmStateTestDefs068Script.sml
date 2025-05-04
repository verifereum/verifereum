open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs068";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/frontier/precompiles/precompile_absence/precompile_absence.json";
val defs = mapi (define_state_test "068") tests;
val () = export_theory_no_docs ();
