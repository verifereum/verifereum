open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1284";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts/sec80.json";
val defs = mapi (define_test "1284") tests;
val () = export_theory_no_docs ();
