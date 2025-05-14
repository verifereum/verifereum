open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0783";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcallcode_101_OOGMBefore.json";
val defs = mapi (define_test "0783") tests;
val () = export_theory_no_docs ();
