open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1012";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log4_Caller.json";
val defs = mapi (define_test "1012") tests;
val () = export_theory_no_docs ();
