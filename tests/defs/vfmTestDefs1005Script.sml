open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1005";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashAccountWithoutCode.json";
val defs = mapi (define_test "1005") tests;
val () = export_theory_no_docs ();
