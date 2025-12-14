open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1095";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log4_emptyMem.json";
val defs = mapi (define_test "1095") tests;
val () = export_theory_no_docs ();
