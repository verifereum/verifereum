open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs043";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_to_tstore_available_at_correct_address.json";
val defs = mapi (define_state_test "043") tests;
val () = export_theory_no_docs ();
