open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0606";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcallcode_101_OOGE.json";
val defs = mapi (define_test "0606") tests;
val () = export_theory_no_docs ();
