open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs195";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip6780_selfdestruct/selfdestruct/create_selfdestruct_same_tx_increased_nonce.json";
val defs = mapi (define_state_test "195") tests;
val () = export_theory_no_docs ();
