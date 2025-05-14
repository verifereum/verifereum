open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1174";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/MSTORE_Bounds2a.json";
val defs = mapi (define_test "1174") tests;
val () = export_theory_no_docs ();
