open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs033";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_multiple_first_valid_authorization_tuples_same_signer.json";
val defs = mapi (define_state_test "033") tests;
val () = export_theory_no_docs ();
