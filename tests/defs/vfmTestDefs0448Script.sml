open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0448";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opc21DiffPlaces.json";
val defs = mapi (define_test "0448") tests;
val () = export_theory_no_docs ();
