open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1999";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shr_-1_255.json";
val defs = mapi (define_test "1999") tests;
val () = export_theory_no_docs ();
