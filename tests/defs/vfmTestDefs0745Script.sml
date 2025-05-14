open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0745";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecallcode_ABCB_RECURSIVE.json";
val defs = mapi (define_test "0745") tests;
val () = export_theory_no_docs ();
