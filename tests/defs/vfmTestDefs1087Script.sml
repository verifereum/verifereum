open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1087";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem32kb+31.json";
val defs = mapi (define_test "1087") tests;
val () = export_theory_no_docs ();
