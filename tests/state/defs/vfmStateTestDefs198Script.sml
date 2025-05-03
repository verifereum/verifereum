open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs198";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip6780_selfdestruct/selfdestruct/create_selfdestruct_same_tx.json";
val defs = mapi (define_state_test "198") tests;
val () = export_theory_no_docs ();
