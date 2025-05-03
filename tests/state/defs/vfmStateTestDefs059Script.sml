open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs059";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_to_contract_creator.json";
val defs = mapi (define_state_test "059") tests;
val () = export_theory_no_docs ();
