open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs013";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage/tload_after_tstore_is_zero.json";
val defs = mapi (define_state_test "013") tests;
val () = export_theory_no_docs ();
