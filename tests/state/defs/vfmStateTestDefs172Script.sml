open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs172";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_to_self_destructing_account_deployed_in_same_tx.json";
val defs = mapi (define_state_test "172") tests;
val () = export_theory_no_docs ();
