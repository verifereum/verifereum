open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0487";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodeDynamicCode2SelfCall.json";
val defs = mapi (define_test "0487") tests;
val () = export_theory_no_docs ();
