open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1052";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/MLOAD_Bounds2.json";
val defs = mapi (define_test "1052") tests;
val () = export_theory_no_docs ();
