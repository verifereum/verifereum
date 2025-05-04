open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs017";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage_reentrancy_contexts/reentrant_call.json";
val defs = mapi (define_state_test "017") tests;
val () = export_theory_no_docs ();
