open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0775";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcall_100_OOGMAfter.json";
val defs = mapi (define_test "0775") tests;
val () = export_theory_no_docs ();
