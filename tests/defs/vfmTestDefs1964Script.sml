open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1964";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar01.json";
val defs = mapi (define_test "1964") tests;
val () = export_theory_no_docs ();
