open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1079";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/log1_dejavu.json";
val defs = mapi (define_test "1079") tests;
val () = export_theory_no_docs ();
