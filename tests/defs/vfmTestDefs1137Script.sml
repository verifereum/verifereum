open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1137";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/stackLimitPush31_1025.json";
val defs = mapi (define_test "1137") tests;
val () = export_theory_no_docs ();
