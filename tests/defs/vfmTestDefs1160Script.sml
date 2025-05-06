open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1160";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/DUP_Bounds.json";
val defs = mapi (define_test "1160") tests;
val () = export_theory_no_docs ();
