open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0481";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opcACDiffPlaces.json";
val defs = mapi (define_test "0481") tests;
val () = export_theory_no_docs ();
