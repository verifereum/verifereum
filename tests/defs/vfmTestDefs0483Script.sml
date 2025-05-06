open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0483";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opcAEDiffPlaces.json";
val defs = mapi (define_test "0483") tests;
val () = export_theory_no_docs ();
