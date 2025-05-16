open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0482";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcodecallcode_011_OOGMBefore.json";
val defs = mapi (define_test "0482") tests;
val () = export_theory_no_docs ();
