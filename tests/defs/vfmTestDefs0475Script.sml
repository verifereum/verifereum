open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0475";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcodecall_010_OOGMBefore.json";
val defs = mapi (define_test "0475") tests;
val () = export_theory_no_docs ();
