open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1011";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log3_nonEmptyMem_logMemSize1_logMemStart31.json";
val defs = mapi (define_test "1011") tests;
val () = export_theory_no_docs ();
