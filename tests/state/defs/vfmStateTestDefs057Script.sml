open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs057";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/delegation_clearing_tx_to.json";
val defs = mapi (define_state_test "057") tests;
val () = export_theory_no_docs ();
