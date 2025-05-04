open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs186";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs_2/contract_storage_to_pointer_with_storage.json";
val defs = mapi (define_state_test "186") tests;
val () = export_theory_no_docs ();
