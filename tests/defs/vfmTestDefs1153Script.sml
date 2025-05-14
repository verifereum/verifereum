open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1153";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CALLCODE_Bounds4.json";
val defs = mapi (define_test "1153") tests;
val () = export_theory_no_docs ();
