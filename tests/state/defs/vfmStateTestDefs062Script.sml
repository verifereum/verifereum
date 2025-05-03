open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs062";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_to_non_empty_storage_non_zero_nonce.json";
val defs = mapi (define_state_test "062") tests;
val () = export_theory_no_docs ();
