open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs008";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tload_reentrancy/tload_reentrancy.json";
val defs = mapi (define_state_test "008") tests;
val () = export_theory_no_docs ();
