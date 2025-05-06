open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0478";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opcA9DiffPlaces.json";
val defs = mapi (define_test "0478") tests;
val () = export_theory_no_docs ();
