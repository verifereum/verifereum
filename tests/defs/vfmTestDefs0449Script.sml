open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0449";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/call_OOG_additionalGasCosts1.json";
val defs = mapi (define_test "0449") tests;
val () = export_theory_no_docs ();
