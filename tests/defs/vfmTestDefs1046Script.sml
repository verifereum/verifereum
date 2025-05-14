open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1046";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashChangedAccount.json";
val defs = mapi (define_test "1046") tests;
val () = export_theory_no_docs ();
