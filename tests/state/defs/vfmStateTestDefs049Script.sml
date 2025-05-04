open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs049";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip6780_selfdestruct/selfdestruct/calling_from_pre_existing_contract_to_new_contract.json";
val defs = mapi (define_state_test "049") tests;
val () = export_theory_no_docs ();
