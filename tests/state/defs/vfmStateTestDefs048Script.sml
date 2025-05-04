open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs048";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip6780_selfdestruct/selfdestruct/calling_from_new_contract_to_pre_existing_contract.json";
val defs = mapi (define_state_test "048") tests;
val () = export_theory_no_docs ();
