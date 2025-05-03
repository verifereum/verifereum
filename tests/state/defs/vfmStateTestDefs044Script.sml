open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs044";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_to_precompile.json";
val defs = mapi (define_state_test "044") tests;
val () = export_theory_no_docs ();
