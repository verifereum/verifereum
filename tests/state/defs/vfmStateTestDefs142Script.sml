open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs142";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/delegation_clearing_tx_to.json";
val defs = mapi (define_state_test "142") tests;
val () = export_theory_no_docs ();
