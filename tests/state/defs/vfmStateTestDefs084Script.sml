open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs084";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/gas/intrinsic_gas_cost.json";
val defs = mapi (define_state_test "084") tests;
val () = export_theory_no_docs ();
