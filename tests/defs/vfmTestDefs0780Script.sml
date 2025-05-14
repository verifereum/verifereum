open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0780";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcallcode_101.json";
val defs = mapi (define_test "0780") tests;
val () = export_theory_no_docs ();
