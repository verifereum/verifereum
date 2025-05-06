open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1996";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/tooLongReturnDataCopy.json";
val defs = mapi (define_test "1996") tests;
val () = export_theory_no_docs ();
