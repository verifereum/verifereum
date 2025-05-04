open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs133";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/gas/self_set_code_cost.json";
val defs = mapi (define_state_test "133") tests;
val () = export_theory_no_docs ();
