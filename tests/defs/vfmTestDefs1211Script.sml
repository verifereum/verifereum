open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1211";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/sha3_dejavu.json";
val defs = mapi (define_test "1211") tests;
val () = export_theory_no_docs ();
