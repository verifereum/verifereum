open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1042";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CREATE_Bounds3.json";
val defs = mapi (define_test "1042") tests;
val () = export_theory_no_docs ();
