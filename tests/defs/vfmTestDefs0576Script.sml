open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0576";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcallcallcode_001_SuicideMiddle.json";
val defs = mapi (define_test "0576") tests;
val () = export_theory_no_docs ();
