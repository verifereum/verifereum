open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2359";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_log0_nonEmptyMem_logMemSize1_logMemStart31.json";
val defs = mapi (define_test "2359") tests;
val () = export_theory_no_docs ();
