open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs132";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/gas/intrinsic_gas_cost.json";
val defs = mapi (define_state_test "132") tests;
val () = export_theory_no_docs ();
