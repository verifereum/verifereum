open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0559";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opcFEDiffPlaces.json";
val defs = mapi (define_test "0559") tests;
val () = export_theory_no_docs ();
