open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0601";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcall_100_OOGMBefore.json";
val defs = mapi (define_test "0601") tests;
val () = export_theory_no_docs ();
