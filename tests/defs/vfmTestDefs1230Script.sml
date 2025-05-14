open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1230";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem64kb-33.json";
val defs = mapi (define_test "1230") tests;
val () = export_theory_no_docs ();
