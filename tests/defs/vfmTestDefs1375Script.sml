open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1375";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallSha256_2.json";
val defs = mapi (define_test "1375") tests;
val () = export_theory_no_docs ();
