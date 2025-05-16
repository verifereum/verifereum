open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0507";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecallcallcode_101_OOGMBefore.json";
val defs = mapi (define_test "0507") tests;
val () = export_theory_no_docs ();
