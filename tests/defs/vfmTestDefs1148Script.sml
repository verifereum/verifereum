open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1148";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CALLCODE_Bounds3.json";
val defs = mapi (define_test "1148") tests;
val () = export_theory_no_docs ();
