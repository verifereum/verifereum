open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs009";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7623_increase_calldata_cost/execution_gas/gas_consumption_below_data_floor.json";
val defs = mapi (define_state_test "009") tests;
val () = export_theory_no_docs ();
