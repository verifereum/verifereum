open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1157";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/DELEGATECALL_Bounds.json";
val defs = mapi (define_test "1157") tests;
val () = export_theory_no_docs ();
