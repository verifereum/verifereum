open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1146";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/static_CALL_Bounds.json";
val defs = mapi (define_test "1146") tests;
val () = export_theory_no_docs ();
