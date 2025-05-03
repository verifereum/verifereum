open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs138";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/frontier/precompiles/precompiles/precompiles.json";
val defs = mapi (define_state_test "138") tests;
val () = export_theory_no_docs ();
