open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs201";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip6780_selfdestruct/reentrancy_selfdestruct_revert/reentrancy_selfdestruct_revert.json";
val defs = mapi (define_state_test "201") tests;
val () = export_theory_no_docs ();
