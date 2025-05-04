open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs202";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/shanghai/eip3855_push0/push0/push0_contracts.json";
val defs = mapi (define_state_test "202") tests;
val () = export_theory_no_docs ();
