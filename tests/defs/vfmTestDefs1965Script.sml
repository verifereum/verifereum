open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1965";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar10.json";
val defs = mapi (define_test "1965") tests;
val () = export_theory_no_docs ();
