open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0697";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcallcode_101_SuicideEnd.json";
val defs = mapi (define_test "0697") tests;
val () = export_theory_no_docs ();
