open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1195";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/log3_dejavu.json";
val defs = mapi (define_test "1195") tests;
val () = export_theory_no_docs ();
