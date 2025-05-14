open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2081";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar00.json";
val defs = mapi (define_test "2081") tests;
val () = export_theory_no_docs ();
