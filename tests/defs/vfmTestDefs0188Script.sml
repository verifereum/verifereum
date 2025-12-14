open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0188";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7883_modexp_gas_increase/test_modexp_different_base_lengths.json";
val defs = mapi (define_test "0188") tests;
val () = export_theory_no_docs ();
