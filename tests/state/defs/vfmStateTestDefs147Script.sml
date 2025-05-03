open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs147";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tload_reentrancy/tload_reentrancy.json";
val defs = mapi (define_state_test "147") tests;
val () = export_theory_no_docs ();
