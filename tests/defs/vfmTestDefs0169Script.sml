open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0169";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7823_modexp_upper_bounds/test_modexp_over_boundary.json";
val defs = mapi (define_test "0169") tests;
val () = export_theory_no_docs ();
