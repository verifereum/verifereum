open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1208";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem32kb-1.json";
val defs = mapi (define_test "1208") tests;
val () = export_theory_no_docs ();
