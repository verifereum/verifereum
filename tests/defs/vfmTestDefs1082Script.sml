open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1082";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/log4_dejavu.json";
val defs = mapi (define_test "1082") tests;
val () = export_theory_no_docs ();
