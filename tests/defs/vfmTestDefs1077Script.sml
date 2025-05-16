open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1077";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/codecopy_dejavu2.json";
val defs = mapi (define_test "1077") tests;
val () = export_theory_no_docs ();
