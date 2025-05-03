open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs157";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage_reentrancy_contexts/reentrant_call.json";
val defs = mapi (define_state_test "157") tests;
val () = export_theory_no_docs ();
