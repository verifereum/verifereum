open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0476";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcodecall_010_SuicideEnd.json";
val defs = mapi (define_test "0476") tests;
val () = export_theory_no_docs ();
