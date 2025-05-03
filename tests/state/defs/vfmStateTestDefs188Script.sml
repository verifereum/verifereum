open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs188";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/point_evaluation_precompile/precompile_before_fork.json";
val defs = mapi (define_state_test "188") tests;
val () = export_theory_no_docs ();
