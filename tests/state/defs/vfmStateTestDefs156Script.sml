open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs156";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage_execution_contexts/subcall.json";
val defs = mapi (define_state_test "156") tests;
val () = export_theory_no_docs ();
