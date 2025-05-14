open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0623";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecallcallcode_101_OOGMAfter.json";
val defs = mapi (define_test "0623") tests;
val () = export_theory_no_docs ();
