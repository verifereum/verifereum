open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1039";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashAccountWithoutCode.json";
val defs = mapi (define_test "1039") tests;
val () = export_theory_no_docs ();
