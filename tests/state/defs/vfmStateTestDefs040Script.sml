open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs040";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/signature_s_out_of_range.json";
val defs = mapi (define_state_test "040") tests;
val () = export_theory_no_docs ();
