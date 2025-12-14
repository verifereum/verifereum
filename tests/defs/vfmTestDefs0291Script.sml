open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0291";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/test_gas_refunds_from_data_floor.json";
val defs = mapi (define_test "0291") tests;
val () = export_theory_no_docs ();
