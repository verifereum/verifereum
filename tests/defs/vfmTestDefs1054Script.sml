open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1054";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/MSTORE_Bounds.json";
val defs = mapi (define_test "1054") tests;
val () = export_theory_no_docs ();
