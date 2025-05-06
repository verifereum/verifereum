open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0527";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opcDADiffPlaces.json";
val defs = mapi (define_test "0527") tests;
val () = export_theory_no_docs ();
