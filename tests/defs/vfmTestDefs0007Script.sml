open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0007";
val tests = json_path_to_tests "../fixtures/blockchain_tests/byzantium/eip196_ec_add_mul/test_gas_costs.json";
val defs = mapi (define_test "0007") tests;
val () = export_theory_no_docs ();
