open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0679";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcodecall_ABCB_RECURSIVE.json";
val defs = mapi (define_test "0679") tests;
val () = export_theory_no_docs ();
