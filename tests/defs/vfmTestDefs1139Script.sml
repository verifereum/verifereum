open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1139";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/stackLimitPush32_1024.json";
val defs = mapi (define_test "1139") tests;
val () = export_theory_no_docs ();
