open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs124";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7623_increase_calldata_cost/refunds/gas_refunds_from_data_floor.json";
val defs = mapi (define_state_test "124") tests;
val () = export_theory_no_docs ();
