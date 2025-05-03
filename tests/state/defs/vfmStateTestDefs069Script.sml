open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs069";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/empty_authorization_list.json";
val defs = mapi (define_state_test "069") tests;
val () = export_theory_no_docs ();
