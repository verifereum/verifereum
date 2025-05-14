open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0547";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opcEADiffPlaces.json";
val defs = mapi (define_test "0547") tests;
val () = export_theory_no_docs ();
