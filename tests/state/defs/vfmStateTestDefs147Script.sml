open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs147";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/set_code_txs/ext_code_on_self_set_code.json";
val defs = mapi (define_state_test "147") tests;
val () = export_theory_no_docs ();
