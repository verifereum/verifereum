open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs146";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tload_calls/tload_calls.json";
val defs = mapi (define_state_test "146") tests;
val () = export_theory_no_docs ();
