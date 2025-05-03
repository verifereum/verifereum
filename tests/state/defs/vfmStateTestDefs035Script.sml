open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs035";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/nonce_overflow_after_first_authorization.json";
val defs = mapi (define_state_test "035") tests;
val () = export_theory_no_docs ();
