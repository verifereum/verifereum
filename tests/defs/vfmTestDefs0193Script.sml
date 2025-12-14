open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0193";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_modexp_variable_gas_cost.json";
val defs = mapi (define_test "0193") tests;
val () = export_theory_no_docs ();
