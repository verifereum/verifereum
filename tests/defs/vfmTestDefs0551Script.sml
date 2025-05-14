open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0551";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opcEEDiffPlaces.json";
val defs = mapi (define_test "0551") tests;
val () = export_theory_no_docs ();
