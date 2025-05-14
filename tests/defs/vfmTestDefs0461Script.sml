open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0461";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opc2ADiffPlaces.json";
val defs = mapi (define_test "0461") tests;
val () = export_theory_no_docs ();
