open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs131";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/gas/gas_cost.json";
val defs = mapi (define_state_test "131") tests;
val () = export_theory_no_docs ();
