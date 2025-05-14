open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1137";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log4_nonEmptyMem.json";
val defs = mapi (define_test "1137") tests;
val () = export_theory_no_docs ();
