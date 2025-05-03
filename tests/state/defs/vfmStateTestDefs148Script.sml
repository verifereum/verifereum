open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs148";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage_selfdestruct/reentrant_selfdestructing_call.json";
val defs = mapi (define_state_test "148") tests;
val () = export_theory_no_docs ();
