open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1324";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/modexpRandomInput.json";
val defs = mapi (define_test "1324") tests;
val () = export_theory_no_docs ();
