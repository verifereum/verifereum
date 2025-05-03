open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs010";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7623_increase_calldata_cost/transaction_validity/transaction_validity_type_4.json";
val defs = mapi (define_state_test "010") tests;
val () = export_theory_no_docs ();
