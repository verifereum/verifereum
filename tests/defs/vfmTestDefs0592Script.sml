open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0592";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcallcodecallcode_011_SuicideEnd.json";
val defs = mapi (define_test "0592") tests;
val () = export_theory_no_docs ();
