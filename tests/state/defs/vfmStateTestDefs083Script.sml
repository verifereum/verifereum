open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs083";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/gas/call_to_pre_authorized_oog.json";
val defs = mapi (define_state_test "083") tests;
val () = export_theory_no_docs ();
