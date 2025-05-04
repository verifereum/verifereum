open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs185";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs_2/call_to_precompile_in_pointer_context.json";
val defs = mapi (define_state_test "185") tests;
val () = export_theory_no_docs ();
