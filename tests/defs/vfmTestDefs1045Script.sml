open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1045";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/DELEGATECALL_Bounds3.json";
val defs = mapi (define_test "1045") tests;
val () = export_theory_no_docs ();
