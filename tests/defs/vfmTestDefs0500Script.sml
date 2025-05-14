open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0500";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opcBBDiffPlaces.json";
val defs = mapi (define_test "0500") tests;
val () = export_theory_no_docs ();
