open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs045";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_using_chain_specific_id.json";
val defs = mapi (define_state_test "045") tests;
val () = export_theory_no_docs ();
