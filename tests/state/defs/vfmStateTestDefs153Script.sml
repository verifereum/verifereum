open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs153";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/basic_tload/basic_tload_after_store.json";
val defs = mapi (define_state_test "153") tests;
val () = export_theory_no_docs ();
