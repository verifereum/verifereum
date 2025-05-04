open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs053";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip6780_selfdestruct/selfdestruct/self_destructing_initcode_create_tx.json";
val defs = mapi (define_state_test "053") tests;
val () = export_theory_no_docs ();
