open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs203";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip6780_selfdestruct/selfdestruct_revert/selfdestruct_not_created_in_same_tx_with_revert.json";
val defs = mapi (define_state_test "203") tests;
val () = export_theory_no_docs ();
