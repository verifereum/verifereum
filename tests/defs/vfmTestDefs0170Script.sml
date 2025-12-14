open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0170";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7823_modexp_upper_bounds/test_modexp_upper_bounds.json";
val defs = mapi (define_test "0170") tests;
val () = export_theory_no_docs ();
