open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1020";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log4_nonEmptyMem_logMemSize1.json";
val defs = mapi (define_test "1020") tests;
val () = export_theory_no_docs ();
