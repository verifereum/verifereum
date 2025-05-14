open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1059";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashDeletedAccountCancun.json";
val defs = mapi (define_test "1059") tests;
val () = export_theory_no_docs ();
