open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1071";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/bufferSrcOffset.json";
val defs = mapi (define_test "1071") tests;
val () = export_theory_no_docs ();
