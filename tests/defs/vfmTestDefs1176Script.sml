open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1176";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/mload32bitBound2.json";
val defs = mapi (define_test "1176") tests;
val () = export_theory_no_docs ();
