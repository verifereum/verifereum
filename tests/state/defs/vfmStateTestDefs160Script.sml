open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs160";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage/transient_storage_unset_values.json";
val defs = mapi (define_state_test "160") tests;
val () = export_theory_no_docs ();
