open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs007";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tload_calls/tload_calls.json";
val defs = mapi (define_state_test "007") tests;
val () = export_theory_no_docs ();
