open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0524";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecallcodecallcode_111_OOGMBefore.json";
val defs = mapi (define_test "0524") tests;
val () = export_theory_no_docs ();
