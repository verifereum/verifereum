open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1238";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallIdentity_2.json";
val defs = mapi (define_test "1238") tests;
val () = export_theory_no_docs ();
