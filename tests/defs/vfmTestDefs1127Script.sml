open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1127";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mload_dejavu.json";
val defs = mapi (define_test "1127") tests;
val () = export_theory_no_docs ();
