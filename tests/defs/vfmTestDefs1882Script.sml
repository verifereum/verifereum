open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1882";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/tooLongReturnDataCopy.json";
val defs = mapi (define_test "1882") tests;
val () = export_theory_no_docs ();
