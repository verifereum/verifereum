open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1179";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem32kb_singleByte-1.json";
val defs = mapi (define_test "1179") tests;
val () = export_theory_no_docs ();
