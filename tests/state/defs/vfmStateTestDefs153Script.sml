open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs153";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/self_sponsored_set_code.json";
val defs = mapi (define_state_test "153") tests;
val () = export_theory_no_docs ();
