open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1072";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/callDataCopyOffset.json";
val defs = mapi (define_test "1072") tests;
val () = export_theory_no_docs ();
