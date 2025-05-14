open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0761";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecall_010_SuicideMiddle.json";
val defs = mapi (define_test "0761") tests;
val () = export_theory_no_docs ();
