open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0495";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opcBADiffPlaces.json";
val defs = mapi (define_test "0495") tests;
val () = export_theory_no_docs ();
