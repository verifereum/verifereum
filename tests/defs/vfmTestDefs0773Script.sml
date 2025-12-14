open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0773";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcodecallcode_111_SuicideMiddle.json";
val defs = mapi (define_test "0773") tests;
val () = export_theory_no_docs ();
