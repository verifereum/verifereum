open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0493";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opcB8DiffPlaces.json";
val defs = mapi (define_test "0493") tests;
val () = export_theory_no_docs ();
