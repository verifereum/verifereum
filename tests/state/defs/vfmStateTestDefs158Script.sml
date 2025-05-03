open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs158";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage/tload_after_sstore.json";
val defs = mapi (define_state_test "158") tests;
val () = export_theory_no_docs ();
