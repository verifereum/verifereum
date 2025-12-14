open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0729";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecall_010_OOGMAfter.json";
val defs = mapi (define_test "0729") tests;
val () = export_theory_no_docs ();
