open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0591";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcodecall_010_OOGMAfter.json";
val defs = mapi (define_test "0591") tests;
val () = export_theory_no_docs ();
