open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs128";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7623_increase_calldata_cost/transaction_validity/transaction_validity_type_4.json";
val defs = mapi (define_state_test "128") tests;
val () = export_theory_no_docs ();
