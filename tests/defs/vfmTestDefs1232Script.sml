open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1232";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverUnrecoverableKey.json";
val defs = mapi (define_test "1232") tests;
val () = export_theory_no_docs ();
