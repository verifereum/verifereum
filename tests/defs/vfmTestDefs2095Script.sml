open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2095";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shiftCombinations.json";
val defs = mapi (define_test "2095") tests;
val () = export_theory_no_docs ();
