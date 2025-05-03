open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs151";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/basic_tload/basic_tload_other_after_tstore.json";
val defs = mapi (define_state_test "151") tests;
val () = export_theory_no_docs ();
