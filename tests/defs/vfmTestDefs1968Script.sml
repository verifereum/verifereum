open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1968";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar_2^254_254.json";
val defs = mapi (define_test "1968") tests;
val () = export_theory_no_docs ();
