open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs075";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_to_precompile_not_enough_gas_for_precompile_execution.json";
val defs = mapi (define_state_test "075") tests;
val () = export_theory_no_docs ();
