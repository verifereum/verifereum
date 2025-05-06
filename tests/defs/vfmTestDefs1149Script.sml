open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1149";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CALLCODE_Bounds4.json";
val defs = mapi (define_test "1149") tests;
val () = export_theory_no_docs ();
