open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0769";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecallcode_ABCB_RECURSIVE.json";
val defs = mapi (define_test "0769") tests;
val () = export_theory_no_docs ();
