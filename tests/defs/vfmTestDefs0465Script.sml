open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0465";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcallcode_001_OOGMBefore.json";
val defs = mapi (define_test "0465") tests;
val () = export_theory_no_docs ();
