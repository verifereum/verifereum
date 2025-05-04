open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs126";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7623_increase_calldata_cost/transaction_validity/transaction_validity_type_1_type_2.json";
val defs = mapi (define_state_test "126") tests;
val () = export_theory_no_docs ();
