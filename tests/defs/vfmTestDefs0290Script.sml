open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0290";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/test_gas_consumption_below_data_floor.json";
val defs = mapi (define_test "0290") tests;
val () = export_theory_no_docs ();
