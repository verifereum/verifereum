open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0501";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecallcall_100_SuicideEnd.json";
val defs = mapi (define_test "0501") tests;
val () = export_theory_no_docs ();
