open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1063";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashSelf.json";
val defs = mapi (define_test "1063") tests;
val () = export_theory_no_docs ();
