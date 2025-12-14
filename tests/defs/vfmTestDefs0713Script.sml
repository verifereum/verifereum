open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0713";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecallcode_111_OOGMBefore.json";
val defs = mapi (define_test "0713") tests;
val () = export_theory_no_docs ();
