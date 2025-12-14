open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0171";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7823_modexp_upper_bounds/test_modexp_upper_bounds_fork_transition.json";
val defs = mapi (define_test "0171") tests;
val () = export_theory_no_docs ();
