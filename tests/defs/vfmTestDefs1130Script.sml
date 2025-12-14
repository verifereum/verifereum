open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1130";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/JUMP_Bounds2.json";
val defs = mapi (define_test "1130") tests;
val () = export_theory_no_docs ();
