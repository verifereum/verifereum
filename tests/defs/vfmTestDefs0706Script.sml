open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0706";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcallcodecallcode_011_OOGE.json";
val defs = mapi (define_test "0706") tests;
val () = export_theory_no_docs ();
