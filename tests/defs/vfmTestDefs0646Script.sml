open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0646";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecallcode_011.json";
val defs = mapi (define_test "0646") tests;
val () = export_theory_no_docs ();
