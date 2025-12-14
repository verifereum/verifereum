open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0192";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_modexp_used_in_transaction_entry_points.json";
val defs = mapi (define_test "0192") tests;
val () = export_theory_no_docs ();
