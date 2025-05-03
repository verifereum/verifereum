open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs008";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7623_increase_calldata_cost/execution_gas/full_gas_consumption.json";
val defs = mapi (define_state_test "008") tests;
val () = export_theory_no_docs ();
