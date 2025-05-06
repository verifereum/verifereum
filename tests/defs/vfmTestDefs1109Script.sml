open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1109";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_emptyMem.json";
val defs = mapi (define_test "1109") tests;
val () = export_theory_no_docs ();
