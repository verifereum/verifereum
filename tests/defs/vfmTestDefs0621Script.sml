open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0621";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_ABCB_RECURSIVE.json";
val defs = mapi (define_test "0621") tests;
val () = export_theory_no_docs ();
