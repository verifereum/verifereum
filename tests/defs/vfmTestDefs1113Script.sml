open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1113";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_nonEmptyMem.json";
val defs = mapi (define_test "1113") tests;
val () = export_theory_no_docs ();
