open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0289";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/test_full_gas_consumption.json";
val defs = mapi (define_test "0289") tests;
val () = export_theory_no_docs ();
