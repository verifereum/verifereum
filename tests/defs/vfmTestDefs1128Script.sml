open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1128";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log3_nonEmptyMem_logMemSize1.json";
val defs = mapi (define_test "1128") tests;
val () = export_theory_no_docs ();
