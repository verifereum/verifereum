open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs122";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7623_increase_calldata_cost/execution_gas/full_gas_consumption.json";
val defs = mapi (define_state_test "122") tests;
val () = export_theory_no_docs ();
