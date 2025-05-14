open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0450";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opc1EDiffPlaces.json";
val defs = mapi (define_test "0450") tests;
val () = export_theory_no_docs ();
