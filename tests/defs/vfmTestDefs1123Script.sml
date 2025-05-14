open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1123";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log3_emptyMem.json";
val defs = mapi (define_test "1123") tests;
val () = export_theory_no_docs ();
