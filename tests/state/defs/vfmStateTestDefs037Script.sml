open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs037";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_multiple_valid_authorization_tuples_same_signer_increasing_nonce_self_sponsored.json";
val defs = mapi (define_state_test "037") tests;
val () = export_theory_no_docs ();
