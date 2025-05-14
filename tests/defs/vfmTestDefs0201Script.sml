open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0201";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/execution_gas/full_gas_consumption.json";
val defs = mapi (define_test "0201") tests;
val () = export_theory_no_docs ();
