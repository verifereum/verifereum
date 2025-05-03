open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs018";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs_2/call_pointer_to_created_from_create_after_oog_call_again.json";
val defs = mapi (define_state_test "018") tests;
val () = export_theory_no_docs ();
