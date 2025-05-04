open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs158";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_from_account_with_non_delegating_code.json";
val defs = mapi (define_state_test "158") tests;
val () = export_theory_no_docs ();
