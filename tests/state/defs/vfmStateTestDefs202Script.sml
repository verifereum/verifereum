open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs202";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip6780_selfdestruct/selfdestruct_revert/selfdestruct_created_in_same_tx_with_revert.json";
val defs = mapi (define_state_test "202") tests;
val () = export_theory_no_docs ();
