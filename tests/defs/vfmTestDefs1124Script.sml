open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1124";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/memReturn.json";
val defs = mapi (define_test "1124") tests;
val () = export_theory_no_docs ();
