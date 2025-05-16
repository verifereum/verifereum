open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2320";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_log0_nonEmptyMem.json";
val defs = mapi (define_test "2320") tests;
val () = export_theory_no_docs ();
