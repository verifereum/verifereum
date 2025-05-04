open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs019";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstore_reentrancy/tstore_reentrancy.json";
val defs = mapi (define_state_test "019") tests;
val () = export_theory_no_docs ();
