open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0953";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashSubcallSuicideCancun.json";
val defs = mapi (define_test "0953") tests;
val () = export_theory_no_docs ();
