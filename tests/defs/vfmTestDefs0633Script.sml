open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0633";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcallcode_001_SuicideEnd.json";
val defs = mapi (define_test "0633") tests;
val () = export_theory_no_docs ();
