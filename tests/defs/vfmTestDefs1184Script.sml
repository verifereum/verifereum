open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1184";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/static_CALL_Bounds.json";
val defs = mapi (define_test "1184") tests;
val () = export_theory_no_docs ();
