open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs186";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/point_evaluation_precompile_gas/point_evaluation_precompile_gas_usage.json";
val defs = mapi (define_state_test "186") tests;
val () = export_theory_no_docs ();
