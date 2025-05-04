open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs150";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/nonce_overflow_after_first_authorization.json";
val defs = mapi (define_state_test "150") tests;
val () = export_theory_no_docs ();
