open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs018";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage_selfdestruct/reentrant_selfdestructing_call.json";
val defs = mapi (define_state_test "018") tests;
val () = export_theory_no_docs ();
