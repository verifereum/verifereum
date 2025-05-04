open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs135";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/call_into_chain_delegating_set_code.json";
val defs = mapi (define_state_test "135") tests;
val () = export_theory_no_docs ();
