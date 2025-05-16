open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1998";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shr_-1_1.json";
val defs = mapi (define_test "1998") tests;
val () = export_theory_no_docs ();
