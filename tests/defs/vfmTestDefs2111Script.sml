open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2111";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shr_-1_0.json";
val defs = mapi (define_test "2111") tests;
val () = export_theory_no_docs ();
