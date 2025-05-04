open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs054";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip6780_selfdestruct/selfdestruct/selfdestruct_pre_existing.json";
val defs = mapi (define_state_test "054") tests;
val () = export_theory_no_docs ();
