open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1068";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extcodehashEmpty_Paris.json";
val defs = mapi (define_test "1068") tests;
val () = export_theory_no_docs ();
