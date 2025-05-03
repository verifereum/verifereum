open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs082";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/gas/gas_cost.json";
val defs = mapi (define_state_test "082") tests;
val () = export_theory_no_docs ();
