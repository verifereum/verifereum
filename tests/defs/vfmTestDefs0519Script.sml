open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0519";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecallcodecall_110_SuicideMiddle.json";
val defs = mapi (define_test "0519") tests;
val () = export_theory_no_docs ();
