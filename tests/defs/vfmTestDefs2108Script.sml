open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2108";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shr01.json";
val defs = mapi (define_test "2108") tests;
val () = export_theory_no_docs ();
