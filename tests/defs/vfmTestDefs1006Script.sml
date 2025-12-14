open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1006";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashCALL.json";
val defs = mapi (define_test "1006") tests;
val () = export_theory_no_docs ();
