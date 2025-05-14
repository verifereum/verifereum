open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0460";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opc29DiffPlaces.json";
val defs = mapi (define_test "0460") tests;
val () = export_theory_no_docs ();
