open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1240";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mload8bitBound.json";
val defs = mapi (define_test "1240") tests;
val () = export_theory_no_docs ();
