open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs002";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/shanghai/eip3855_push0/push0/push0_contract_during_call_contexts.json";
val defs = mapi (define_state_test "002") tests;
val () = export_theory_no_docs ();
