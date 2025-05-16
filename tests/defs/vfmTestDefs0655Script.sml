open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0655";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecall_10_SuicideEnd.json";
val defs = mapi (define_test "0655") tests;
val () = export_theory_no_docs ();
