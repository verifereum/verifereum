open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs123";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7623_increase_calldata_cost/execution_gas/gas_consumption_below_data_floor.json";
val defs = mapi (define_state_test "123") tests;
val () = export_theory_no_docs ();
