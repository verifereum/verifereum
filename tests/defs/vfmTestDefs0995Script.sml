open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0995";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_emptyMem.json";
val defs = mapi (define_test "0995") tests;
val () = export_theory_no_docs ();
