open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0594";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcallcodecallcode_ABCB_RECURSIVE.json";
val defs = mapi (define_test "0594") tests;
val () = export_theory_no_docs ();
