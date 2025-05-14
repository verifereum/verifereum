open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1246";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mstore_dejavu.json";
val defs = mapi (define_test "1246") tests;
val () = export_theory_no_docs ();
