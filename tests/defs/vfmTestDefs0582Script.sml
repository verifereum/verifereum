open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0582";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcallcodecall_010_OOGE.json";
val defs = mapi (define_test "0582") tests;
val () = export_theory_no_docs ();
