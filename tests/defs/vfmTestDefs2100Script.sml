open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2100";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shiftSignedCombinations.json";
val defs = mapi (define_test "2100") tests;
val () = export_theory_no_docs ();
