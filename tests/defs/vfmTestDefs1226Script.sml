open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1226";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverCheckLength.json";
val defs = mapi (define_test "1226") tests;
val () = export_theory_no_docs ();
