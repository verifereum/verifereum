open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0672";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcode_11_SuicideEnd.json";
val defs = mapi (define_test "0672") tests;
val () = export_theory_no_docs ();
