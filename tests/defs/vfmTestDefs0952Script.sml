open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0952";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashSubcallSuicide.json";
val defs = mapi (define_test "0952") tests;
val () = export_theory_no_docs ();
