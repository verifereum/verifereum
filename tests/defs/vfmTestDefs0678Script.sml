open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0678";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcodecall_110_SuicideMiddle.json";
val defs = mapi (define_test "0678") tests;
val () = export_theory_no_docs ();
