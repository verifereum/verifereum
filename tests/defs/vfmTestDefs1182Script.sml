open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1182";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/mload32bitBound_return.json";
val defs = mapi (define_test "1182") tests;
val () = export_theory_no_docs ();
