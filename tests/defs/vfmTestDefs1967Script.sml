open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1967";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar_0_256-1.json";
val defs = mapi (define_test "1967") tests;
val () = export_theory_no_docs ();
