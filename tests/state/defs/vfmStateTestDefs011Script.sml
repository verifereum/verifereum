open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs011";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage/tload_after_sstore.json";
val defs = mapi (define_state_test "011") tests;
val () = export_theory_no_docs ();
