open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1386";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/modexp_0_0_0_22000.json";
val defs = mapi (define_test "1386") tests;
val () = export_theory_no_docs ();
