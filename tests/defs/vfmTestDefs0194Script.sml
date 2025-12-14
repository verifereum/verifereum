open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0194";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_modexp_variable_gas_cost_exceed_tx_gas_cap.json";
val defs = mapi (define_test "0194") tests;
val () = export_theory_no_docs ();
