open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0675";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcodecall_110_OOGMAfter.json";
val defs = mapi (define_test "0675") tests;
val () = export_theory_no_docs ();
