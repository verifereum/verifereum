open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1162";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/DELEGATECALL_Bounds2.json";
val defs = mapi (define_test "1162") tests;
val () = export_theory_no_docs ();
