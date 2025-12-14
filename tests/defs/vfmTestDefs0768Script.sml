open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0768";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcodecallcode_111.json";
val defs = mapi (define_test "0768") tests;
val () = export_theory_no_docs ();
