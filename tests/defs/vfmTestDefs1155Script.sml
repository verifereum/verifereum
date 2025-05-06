open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1155";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CREATE_Bounds2.json";
val defs = mapi (define_test "1155") tests;
val () = export_theory_no_docs ();
