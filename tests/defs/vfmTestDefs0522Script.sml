open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0522";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/opcD5DiffPlaces.json";
val defs = mapi (define_test "0522") tests;
val () = export_theory_no_docs ();
