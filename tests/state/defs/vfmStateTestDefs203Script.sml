open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs203";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/shanghai/eip3860_initcode/initcode/contract_creating_tx.json";
val defs = mapi (define_state_test "203") tests;
val () = export_theory_no_docs ();
