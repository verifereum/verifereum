open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0459";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opc28DiffPlaces.json";
val defs = mapi (define_test "0459") tests;
val () = export_theory_no_docs ();
