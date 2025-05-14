open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1057";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashDeletedAccount3.json";
val defs = mapi (define_test "1057") tests;
val () = export_theory_no_docs ();
