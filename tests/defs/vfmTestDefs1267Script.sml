open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1267";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/modexp_0_0_0_20500.json";
val defs = mapi (define_test "1267") tests;
val () = export_theory_no_docs ();
