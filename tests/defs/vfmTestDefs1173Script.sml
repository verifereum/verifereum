open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1173";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/SLOAD_Bounds.json";
val defs = mapi (define_test "1173") tests;
val () = export_theory_no_docs ();
