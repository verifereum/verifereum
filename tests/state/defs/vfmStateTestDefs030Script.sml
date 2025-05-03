open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs030";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_address_and_authority_warm_state.json";
val defs = mapi (define_state_test "030") tests;
val () = export_theory_no_docs ();
