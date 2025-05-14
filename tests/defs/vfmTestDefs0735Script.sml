open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0735";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_110_OOGMBefore.json";
val defs = mapi (define_test "0735") tests;
val () = export_theory_no_docs ();
